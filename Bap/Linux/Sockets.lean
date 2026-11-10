import Bap.Linux.Kernel

/-! # Sockets of the Unix domain, and of the Internet in here

Sockets of `AF_INET` and `AF_INET6` are TCP and UDP between the processes of the machine, on its loopback, as nothing here reaches
the machine that this runs on: an address of the Internet is one of 127.0.0.0/8 or `::1`, or any of them. TCP is a stream and UDP
datagrams, as they are of the Unix domain, but for a datagram to a port that nobody has, which is gone, as Linux has it.

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

/-- What the socket of an inode is now. An inode that isn't there stays not there. -/
def setSocket (kernel : Kernel) (number : Nat) (socket : Socket) : Kernel :=
  kernel.setContent number (.socket socket)

/-- The socket of a descriptor, with its inode. -/
def socketOf (kernel : Kernel) (group fd : Nat) : Result (Nat × Socket) := do
  let (_, file) ← openFileOf kernel group fd
  match kernel.socketAt file.inode with
  | some socket => .ok (file.inode, socket)
  | none => .error Errno.enotsock

/-- Whether a descriptor is of a socket, for `read` and `write` to go to it. -/
def isSocket (kernel : Kernel) (group fd : Nat) : Bool :=
  match kernel.socketOf group fd with
  | .ok _ => true
  | .error _ => false

/-- Whether a socket is there for the other end: a live process holds it, as `heldFiles` has it, or a listener that one holds has it to
accept. A connection that its listener went with before it was accepted is gone, as Linux has it. -/
def socketAlive (kernel : Kernel) (number : Nat) (groups : List Nat) : Bool :=
  kernel.pipeHeld number groups true || (kernel.socketAt number |>.any (·.waiting)) &&
    kernel.inodes.fold (init := false) fun found listener inode =>
      found || match inode.content with
        | .socket socket => socket.pending.contains number && kernel.pipeHeld listener groups true
        | _ => false

/-- Whether the other end of a connection was reset, which a read that has nothing else to read tells once, as `ECONNRESET`: it is
gone, and it went with what it hadn't read, or before it was accepted, as Linux has it. -/
def wasReset (kernel : Kernel) (socket : Socket) (alive : Nat → Bool) : Bool :=
  socket.type != 2 && match socket.peer with
    | some peer => !alive peer && (kernel.socketAt peer |>.any fun other => other.waiting || !other.incoming.isEmpty)
    | none => false

/-- If the connection of a descriptor was reset and it has nothing to read, the kernel once that is told: the other end has nothing any
more, as Linux throws away what it had. -/
def tellReset (kernel : Kernel) (group fd : Nat) (alive : Nat → Bool) : Option Kernel := do
  let (_, socket) ← (kernel.socketOf group fd).toOption
  if !socket.incoming.isEmpty || !kernel.wasReset socket alive then none
  let peer ← socket.peer
  let other ← kernel.socketAt peer
  some (kernel.setSocket peer { other with incoming := #[], waiting := false })

/-- A new socket, of the user and the group of the filesystem of the process that it is of, as Linux has it. -/
private def newSocket (kernel : Kernel) (socket : Socket) : Kernel × Nat :=
  let number := kernel.nextInode
  ({ kernel with
      inodes := kernel.inodes.insert number
        { number, content := .socket socket, mode := 0o140777, details := kernel.madeBy (kernel.process socket.owner).credentials }
      nextInode := number + 1 }, number)

/-- A descriptor of a socket, with `O_NONBLOCK` and `O_CLOEXEC` of `flags`. -/
private def openSocket (kernel : Kernel) (group number flags : Nat) : Kernel × Nat :=
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := 2 ||| (flags &&& oNonblock) }
    nextOpenFile := openFile + 1 }
  kernel.addDescriptor group openFile (flags &&& oCloexec != 0)

/-- `socket`, of a type as 1, 2 or 5, with flags as `open` has them. -/
def socket (kernel : Kernel) (group type flags : Nat) (family : Nat := 1) : Kernel × Nat :=
  let (kernel, number) := newSocket kernel { type, owner := group, family }
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
  if socket.family != 1 then .error Errno.eafnosupport
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
  .ok ((kernel.bindPath key number).setSocket number { socket with name := some name })

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
def connect (kernel : Kernel) (group fd target : Nat) (alive : Nat → Bool) (serverName : Option String := none) : Result Kernel := do
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
      { type := socket.type, name := serverName <|> listener.name, peer := some number, waiting := true, owner := listener.owner
        family := socket.family }
    let kernel := kernel.setSocket number { socket with peer := some server, owner := group }
    .ok (kernel.setSocket target { listener with pending := listener.pending ++ [server] })

/-- `accept`: a descriptor of the first connection that is waiting, with its end here, or none if there is none yet. -/
def accept (kernel : Kernel) (group fd flags : Nat) : Result (Kernel × Option (Nat × Nat)) := do
  let (number, socket) ← socketOf kernel group fd
  if !socket.listening then .error Errno.einval
  match socket.pending with
  -- A listener that `shutdown` shut takes no more: what waits there is `EINVAL`, as Linux's `unix_accept` and `inet_accept` have it.
  | [] => if socket.readShut then .error Errno.einval else .ok (kernel, none)
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
  let (number, socket) ← socketOf kernel group fd
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
    -- A socket that is connected takes datagrams only from the one that it is connected to.
    if receiver.peer.any (· != number) then .error Errno.eperm
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
def receive (kernel : Kernel) (group fd count : Nat) (peek : Bool) (alive : Nat → Bool) (all : Bool := false) :
    Result (Kernel × Option Received) := do
  let (number, socket) ← socketOf kernel group fd
  let ended : Bool := socket.readShut ||
    (socket.type != 2 && match socket.peer with
      | some peer => !alive peer || (kernel.socketAt peer |>.any (·.writeShut))
      | none => false)
  -- `MSG_WAITALL` of a stream that may have more: all that it asks for, or it waits, as Linux has it of one that may wait.
  if all && !peek && socket.type == 1 && !ended && (socket.incoming.foldl (· + ·.data.size) 0) < count then return (kernel, none)
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
  -- Linux's `unix_shutdown` has no `ENOTCONN`; `inet_shutdown` has it of what is neither connected nor listening.
  if socket.family != 1 && socket.peer.isNone && socket.remote.isNone && socket.type != 2 && !socket.listening then .error Errno.enotconn
  .ok (kernel.setSocket number { socket with
    readShut := socket.readShut || how != 1, writeShut := socket.writeShut || how != 0 })

/-- The name of the socket at the other end, for `getpeername`. -/
def peerName (kernel : Kernel) (group fd : Nat) : Result (Option String) := do
  let (_, socket) ← socketOf kernel group fd
  match socket.peer, socket.remote with
  | some peer, _ => .ok ((kernel.socketAt peer).bind (·.name))
  | none, some remote => .ok (some remote)
  | none, none => .error Errno.enotconn

/-- Open files handed over, as descriptors of `group`. -/
def receiveRights (kernel : Kernel) (group : Nat) (rights : List Nat) (closeOnExec : Bool) : Kernel × List Nat :=
  rights.foldl (init := (kernel, [])) fun (kernel, fds) openFile =>
    let (kernel, fd) := kernel.addDescriptor group openFile closeOnExec
    (kernel, fds ++ [fd])

/-- The open files of descriptors, to hand over. -/
def rightsOf (kernel : Kernel) (group : Nat) (fds : List Nat) : Result (List Nat) :=
  fds.mapM fun fd => do pure (← openFileOf kernel group fd).1

/-! ### The Internet in here -/

/-- An address of the Internet: its family, 2 or 10, the number of the address and a port. -/
structure Endpoint where
  family : Nat
  address : Nat
  port : Nat
  deriving DecidableEq, Repr

namespace Endpoint

/-- What a socket has as its name, which is no path and no name of the Unix domain. -/
def name (endpoint : Endpoint) : String := s!"\x01{endpoint.family}:{endpoint.address}:{endpoint.port}"

/-- The address that a name of a socket is, if it is of the Internet. -/
def ofName? (name : String) : Option Endpoint :=
  if !name.startsWith "\x01" then none
  else
    match ((name.drop 1).toString.splitOn ":").map String.toNat? with
    | [some family, some address, some port] => some { family, address, port }
    | _ => none

/-- `127.0.0.1` or `::1`, which is where an address of any of them goes. -/
def loopback (family : Nat) : Nat := if family == 2 then 0x7f000001 else 1

/-- Whether it is an address of the machine, or any of them. -/
def isLocal (endpoint : Endpoint) : Bool :=
  endpoint.address == 0 || (if endpoint.family == 2 then endpoint.address >>> 24 == 127 else endpoint.address == 1)

/-- Where a socket of a type is bound to it, among the names of the kernel. -/
def key (type : Nat) (endpoint : Endpoint) : String :=
  s!"\x01{type}/{endpoint.family}:{endpoint.address}:{endpoint.port}"

/-- The type of socket and the address that a key of `key` is, if it is one. -/
def ofKey? (key : String) : Option (Nat × Endpoint) :=
  if !key.startsWith "\x01" then none
  else
    match (key.drop 1).toString.splitOn "/" with
    | [type, rest] =>
      match type.toNat?, ofName? ("\x01" ++ rest) with
      | some type, some endpoint => some (type, endpoint)
      | _, _ => none
    | _ => none

end Endpoint

/-- The ports of a type and family that sockets that are still there have. -/
private def usedPorts (kernel : Kernel) (type family : Nat) (alive : Nat → Bool) : Std.HashSet Nat :=
  kernel.paths.fold (init := {}) fun used key number =>
    match Endpoint.ofKey? key with
    | some (kind, endpoint) => if kind == type && endpoint.family == family && alive number then used.insert endpoint.port else used
    | none => used

/-- A port that none has, from those that Linux gives out, 32768 to 60999. -/
def freePort (kernel : Kernel) (type family : Nat) (alive : Nat → Bool) : Nat :=
  let used := kernel.usedPorts type family alive
  ((List.range 28232).find? fun index => !used.contains (32768 + index)).map (32768 + ·) |>.getD 0

/-- A socket of the Internet without a name gets a port of its own on the loopback, as one does that connects or sends first. -/
def autobind (kernel : Kernel) (number : Nat) (socket : Socket) (alive : Nat → Bool) : Kernel × Socket :=
  if socket.name.isSome || socket.family == 1 then (kernel, socket)
  else
    let endpoint : Endpoint := { family := socket.family, address := Endpoint.loopback socket.family
                                 port := kernel.freePort socket.type socket.family alive }
    let socket := { socket with name := some endpoint.name }
    ({ kernel with paths := kernel.paths.insert (endpoint.key socket.type) number }.setSocket number socket, socket)

/-- `bind` of a socket of the Internet: to an address of the machine or to all of them, and to a port that no other has there, or to
one that none has of port 0. -/
def bindInet (kernel : Kernel) (group fd : Nat) (endpoint : Endpoint) (alive : Nat → Bool) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  if socket.family != endpoint.family then .error Errno.eafnosupport
  if socket.name.isSome then .error Errno.einval
  if !endpoint.isLocal then .error Errno.eaddrnotavail
  let endpoint := { endpoint with port := if endpoint.port == 0 then kernel.freePort socket.type endpoint.family alive else endpoint.port }
  let clash := kernel.paths.toList.any fun (key, other) =>
    match Endpoint.ofKey? key with
    | some (type, bound) =>
      type == socket.type && bound.family == endpoint.family && bound.port == endpoint.port && alive other &&
        (bound.address == endpoint.address || bound.address == 0 || endpoint.address == 0)
    | none => false
  if clash then .error Errno.eaddrinuse
  .ok ({ kernel with paths := kernel.paths.insert (endpoint.key socket.type) number }.setSocket number
    { socket with name := some endpoint.name })

/-- The socket of a type that has an address: one bound to it, or else to all addresses of its port. Any address is the loopback. -/
def socketAtEndpoint (kernel : Kernel) (type : Nat) (endpoint : Endpoint) (alive : Nat → Bool) : Option Nat :=
  let address := if endpoint.address == 0 then Endpoint.loopback endpoint.family else endpoint.address
  match (kernel.paths.get? ({ endpoint with address }.key type)).filter alive with
  | some number => some number
  | none => (kernel.paths.get? ({ endpoint with address := 0 }.key type)).filter alive

/-- Where a connection or a datagram goes: the address, with any address as the loopback, which has to be of the machine. -/
private def destination (endpoint : Endpoint) : Result Endpoint :=
  if !endpoint.isLocal then .error Errno.enetunreach
  else .ok { endpoint with address := if endpoint.address == 0 then Endpoint.loopback endpoint.family else endpoint.address }

/-- `connect` of a socket of the Internet. A stream connects to what listens there, which has a connection to accept whose end there
has the address that was asked for. Datagrams go there from then, to whoever has it. -/
def connectInet (kernel : Kernel) (group fd : Nat) (endpoint : Endpoint) (alive : Nat → Bool) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  if socket.family != endpoint.family then .error Errno.eafnosupport
  let target ← destination endpoint
  let (kernel, socket) := kernel.autobind number socket alive
  if socket.type == 2 then .ok (kernel.setSocket number { socket with remote := some target.name })
  else
    match kernel.socketAtEndpoint socket.type target alive with
    | none => .error Errno.econnrefused
    | some listener => kernel.connect group fd listener alive (serverName := some target.name)

/-- `listen` of a socket of the Internet, which has a port of its own if it had none. -/
def listenInet (kernel : Kernel) (group fd : Nat) (alive : Nat → Bool) : Result Kernel := do
  let (number, socket) ← socketOf kernel group fd
  let (kernel, _) := kernel.autobind number socket alive
  kernel.listen group fd

/-- A datagram of the Internet, to `endpoint` or to where the socket was connected. If nobody has that address, or the socket there is
connected to another, it is gone, and it went. -/
def sendDatagram (kernel : Kernel) (group fd : Nat) (data : ByteArray) (endpoint : Option Endpoint) (alive : Nat → Bool) :
    Result (Kernel × Nat) := do
  let (number, socket) ← socketOf kernel group fd
  if socket.writeShut then .error Errno.epipe
  let wanted ← match endpoint, socket.remote.bind Endpoint.ofName? with
    | some endpoint, _ => .ok endpoint
    | none, some remote => .ok remote
    | none, none => .error Errno.edestaddrreq
  if wanted.family != socket.family then .error Errno.eafnosupport
  let target ← destination wanted
  let (kernel, socket) := kernel.autobind number socket alive
  -- Where it is from, with any address as the loopback, as a socket that is connected has where it is connected to.
  let source := (socket.name.bind Endpoint.ofName?).map fun endpoint =>
    { endpoint with address := if endpoint.address == 0 then Endpoint.loopback endpoint.family else endpoint.address }
  match (kernel.socketAtEndpoint 2 target alive).bind fun receiver => (kernel.socketAt receiver).map (receiver, ·) with
  | some (receiver, other) =>
    if other.remote.isSome && other.remote != source.map (·.name) then .ok (kernel, data.size)
    else .ok (kernel.setSocket receiver { other with incoming := other.incoming.push { data, sender := socket.name } }, data.size)
  | none => .ok (kernel, data.size)

end Kernel

end Bap.Linux
