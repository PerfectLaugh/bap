open Core

let b ~pc target =
  if Int64.(pc land 3L <> 0L) then
    invalid_arg "Bap_emu.AArch64.b: branch instruction PC is not 4-byte aligned";
  let displacement = Int64.(target - pc) in
  if
    Int64.(
      displacement land 3L <> 0L
      || displacement < -0x8000000L || displacement > 0x7fffffcL)
  then
    invalid_arg
      "Bap_emu.AArch64.b: target is outside the aligned signed 28-bit byte \
       range";
  let immediate = Int64.(to_int32_trunc (displacement / 4L)) in
  Int32.(0x14000000l lor (immediate land 0x03ffffffl))

let ret = 0xd65f03c0l

let bytes word =
  let bytes = Stdlib.Bytes.create 4 in
  Stdlib.Bytes.set_int32_le bytes 0 word;
  Stdlib.Bytes.to_string bytes
