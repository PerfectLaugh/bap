import Bap.Linux.Kernel

/-! # Sockets of the Unix domain

What a program does with sockets of `AF_UNIX`: streams, datagrams and sequenced packets, bound to a path or to a name of their own,
connected in pairs or by `listen`, `connect` and `accept`, with open files handed over. A socket is an inode, and what it holds is in
it, so that a checkpoint has it as it has a pipe. Whether the other end is still there is whether a live process has a descriptor of
it, which `Machine` says, as it does of a pipe. Nothing here waits: what would is told, and `Machine` waits. -/

namespace Bap.Linux

namespace Kernel

/-- The socket of an inode, if it is one. -/
def socketAt (kernel : Kernel) (number : Nat) : Option Socket :=
  match kernel.inodes.get? number with
  | some { content := .socket socket, .. } => some socket
  | _ => none

def setSocket (kernel : Kernel) (number : Nat) (socket : Socket) : Kernel :=
  match kernel.inodes.get? number with
  | some inode => { kernel with inodes := kernel.inodes.insert number { inode with content := .socket socket } }
  | none => kernel

/-- The socket of a descriptor, with its inode. -/
def socketOf (kernel : Kernel) (group fd : Nat) : Result (Nat × Socket) := do
  let (_, file) ← openFileOf kernel group fd
  match kernel.socketAt file.inode with
  | some socket => .ok (file.inode, socket)
  | none => .error Errno.enotsock

def isSocket (kernel : Kernel) (group fd : Nat) : Bool :=
  match kernel.socketOf group fd with
  | .ok _ => true
  | .error _ => false

/-- Whether a socket is there for the other end: a descriptor of a live process has it, or a listener has it to accept. -/
def socketAlive (kernel : Kernel) (number : Nat) (groups : List Nat) : Bool :=
  kernel.pipeHeld number groups true || (kernel.socketAt number |>.any (·.waiting))

private def newSocket (kernel : Kernel) (socket : Socket) : Kernel × Nat :=
  let number := kernel.nextInode
  ({ kernel with
      inodes := kernel.inodes.insert number { number, content := .socket socket, mode := 0o140777 }
      nextInode := number + 1 }, number)

/-- A descriptor of a socket, with `O_NONBLOCK` and `O_CLOEXEC` of `flags`. -/
private def openSocket (kernel : Kernel) (group number flags : Nat) : Kernel × Nat :=
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := 2 ||| (flags &&& oNonblock) }
    nextOpenFile := openFile + 1 }
  kernel.addDescriptor group openFile (flags &&& oCloexec != 0)

/-- `socket`, of a type as 1, 2 or 5, with flags as `open` has them. -/
def socket (kernel : Kernel) (group type flags : Nat) : Kernel × Nat :=
  let (kernel, number) := newSocket kernel { type, owner := group }
  openSocket kernel group number flags

/-- `socketpair`: two sockets, each the other's peer. -/
def socketPair (kernel : Kernel) (group type flags : Nat) : Kernel × Nat × Nat :=
  let first := kernel.nextInode
  let (kernel, _) := newSocket kernel { type, peer := some (first + 1), owner := group }
  let (kernel, second) := newSocket kernel { type, peer := some first, owner := group }
  let (kernel, one) := openSocket kernel group first flags
  let (kernel, other) := openSocket kernel group second flags
  (kernel, one, other)

/-- Whether a name is one of its own and not a path: it starts with a zero byte. -/
def abstractName (name : String) : Bool := name.startsWith "\x00"

/-- `bind`. A path mustn't be there yet, and its directory must. A name of its own that a socket nobody has any more had is free. -/
def bind (kernel : Kernel) (group fd : Nat) (base name : String) (alive : Nat → Bool) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  if socket.name.isSome then .error Errno.einval
  let key ← if abstractName name then
      match kernel.paths.get? name with
      | some other => if alive other then .error Errno.eaddrinuse else .ok name
      | none => .ok name
    else do
      if name == "" then .error Errno.einval
      let (normal, found) ← kernel.resolve base name (follow := false)
      if found.isSome then .error Errno.eaddrinuse
      match kernel.paths.get? (Path.parent normal) with
      | some directory =>
        match kernel.inodes.get? directory with
        | some { content := .directory, .. } => .ok normal
        | _ => .error Errno.enoent
      | none => .error Errno.enoent
  .ok ({ kernel with paths := kernel.paths.insert key number }.setSocket number { socket with name := some name })

/-- The socket that a name is bound to. A path that isn't there is `ENOENT`, and one that isn't a socket can't be connected to. -/
def socketNamed (kernel : Kernel) (base name : String) : Result Nat := do
  let found ← if abstractName name then .ok (kernel.paths.get? name)
    else do
      if name == "" then .error Errno.enoent
      let (_, found) ← kernel.resolve base name
      if found.isNone then .error Errno.enoent
      .ok found
  match found with
  | some number => if (kernel.socketAt number).isSome then .ok number else .error Errno.econnrefused
  | none => .error Errno.econnrefused

/-- `listen`, of a stream or of sequenced packets. -/
def listen (kernel : Kernel) (group fd : Nat) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  if socket.type == 2 then .error Errno.eopnotsupp
  if socket.peer.isSome then .error Errno.einval
  .ok (kernel.setSocket number { socket with listening := true, owner := group })

/-- `connect` to the socket `target`. Of datagrams, it is where they go when a send doesn't say. Otherwise the listener has a new
connection to accept, whose end there is connected already, as Linux has it when the backlog has room, which here it always has. -/
def connect (kernel : Kernel) (group fd target : Nat) (alive : Nat → Bool) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  let some listener := kernel.socketAt target | .error Errno.econnrefused
  if listener.type != socket.type then .error Errno.eprototype
  if socket.type == 2 then
    .ok (kernel.setSocket number { socket with peer := some target })
  else
    if socket.peer.isSome then .error Errno.eisconn
    if socket.listening then .error Errno.einval
    if !listener.listening || !alive target then .error Errno.econnrefused
    let (kernel, server) := newSocket kernel
      { type := socket.type, name := listener.name, peer := some number, waiting := true, owner := listener.owner }
    let kernel := kernel.setSocket number { socket with peer := some server, owner := group }
    .ok (kernel.setSocket target { listener with pending := listener.pending ++ [server] })

/-- `accept`: a descriptor of the first connection that is waiting, with its end here, or none if there is none yet. -/
def accept (kernel : Kernel) (group fd flags : Nat) : Result (Kernel × Option (Nat × Nat)) := do
  let (number, socket) ← socketOf kernel group fd
  if !socket.listening then .error Errno.einval
  match socket.pending with
  | [] => .ok (kernel, none)
  | server :: rest =>
    let kernel := kernel.setSocket number { socket with pending := rest }
    let kernel := match kernel.socketAt server with
      | some accepted => kernel.setSocket server { accepted with waiting := false }
      | none => kernel
    let (kernel, accepted) := openSocket kernel group server flags
    .ok (kernel, some (accepted, server))

/-- `send` and its kin: a message to the other end, or of datagrams to `target` if it says. It is how many bytes went. -/
def send (kernel : Kernel) (group fd : Nat) (message : Message) (target : Option Nat) (alive : Nat → Bool) :
    Result (Kernel × Nat) := do
  let (_, socket) ← socketOf kernel group fd
  if socket.writeShut then .error Errno.epipe
  let message := { message with sender := socket.name }
  if socket.type == 2 then
    let destination ← match target, socket.peer with
      | some target, _ => .ok target
      | none, some peer => .ok peer
      | none, none => .error Errno.enotconn
    let some receiver := kernel.socketAt destination | .error Errno.econnrefused
    if receiver.type != 2 then .error Errno.eprototype
    if !alive destination then .error Errno.econnrefused
    .ok (kernel.setSocket destination { receiver with incoming := receiver.incoming.push message }, message.data.size)
  else
    if target.isSome && socket.peer.isSome then .error Errno.eisconn
    let some peer := socket.peer | .error Errno.enotconn
    let some other := kernel.socketAt peer | .error Errno.econnreset
    if !alive peer || other.readShut then .error Errno.epipe
    if message.data.size == 0 && message.rights.isEmpty && socket.type == 1 then .ok (kernel, 0) else
    .ok (kernel.setSocket peer { other with incoming := other.incoming.push message }, message.data.size)

/-- What a receive got: the bytes, who sent them if it had a name, the open files that came with them, and how big the message was,
which is more than the bytes when a datagram didn't fit. -/
structure Received where
  data : ByteArray
  sender : Option String := none
  rights : List Nat := []
  size : Nat

/-- `recv` and its kin: up to `count` bytes, or none if there is nothing yet and the other end may still send. A stream gives what has
come in order, as far as the open files of a message that comes after the first: those come with the bytes that they came with. A
message of the others comes whole, but for what doesn't fit, which is gone. At the end of a stream, it is nothing. With `peek` it stays. -/
def receive (kernel : Kernel) (group fd count : Nat) (peek : Bool) (alive : Nat → Bool) : Result (Kernel × Option Received) := do
  let (number, socket) ← socketOf kernel group fd
  let ended : Bool := socket.readShut ||
    (socket.type != 2 && match socket.peer with
      | some peer => !alive peer || (kernel.socketAt peer |>.any (·.writeShut))
      | none => false)
  if socket.incoming.isEmpty then
    if ended then return (kernel, some { data := ByteArray.empty, size := 0 })
    if socket.type != 2 && socket.peer.isNone then .error Errno.enotconn
    return (kernel, none)
  if socket.type != 1 then
    let message := socket.incoming[0]!
    let kept := if peek then socket.incoming else socket.incoming.extract 1 socket.incoming.size
    return (kernel.setSocket number { socket with incoming := kept },
      some { data := message.data.extract 0 count, sender := message.sender, rights := message.rights, size := message.data.size })
  -- A stream, from as many messages as it takes.
  let mut data := ByteArray.empty
  let mut rights : List Nat := []
  let mut taken := 0
  let mut rest := socket.incoming
  for message in socket.incoming do
    if data.size ≥ count then break
    if taken > 0 && !message.rights.isEmpty then break
    let piece := message.data.extract 0 (count - data.size)
    data := data ++ piece
    if taken == 0 then rights := message.rights
    taken := taken + 1
    rest := if piece.size < message.data.size then
        #[{ message with data := message.data.extract piece.size message.data.size, rights := [] }] ++ rest.extract 1 rest.size
      else rest.extract 1 rest.size
  let incoming := if peek then socket.incoming else rest
  .ok (kernel.setSocket number { socket with incoming }, some { data, rights, size := data.size })

/-- `shutdown`: 0 for reading, 1 for writing, 2 for both. -/
def shutdown (kernel : Kernel) (group fd how : Nat) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  if how > 2 then .error Errno.einval
  if socket.peer.isNone && socket.type != 2 then .error Errno.enotconn
  .ok (kernel.setSocket number { socket with
    readShut := socket.readShut || how != 1, writeShut := socket.writeShut || how != 0 })

/-- The name of the socket at the other end, for `getpeername`. -/
def peerName (kernel : Kernel) (group fd : Nat) : Result (Option String) := do
  let (_, socket) ← socketOf kernel group fd
  let some peer := socket.peer | .error Errno.enotconn
  .ok ((kernel.socketAt peer).bind (·.name))

/-- Open files handed over, as descriptors of `group`. -/
def receiveRights (kernel : Kernel) (group : Nat) (rights : List Nat) (closeOnExec : Bool) : Kernel × List Nat :=
  rights.foldl (init := (kernel, [])) fun (kernel, fds) openFile =>
    let (kernel, fd) := kernel.addDescriptor group openFile closeOnExec
    (kernel, fds ++ [fd])

/-- The open files of descriptors, to hand over. -/
def rightsOf (kernel : Kernel) (group : Nat) (fds : List Nat) : Result (List Nat) :=
  fds.mapM fun fd => do pure (← openFileOf kernel group fd).1

end Kernel

end Bap.Linux
