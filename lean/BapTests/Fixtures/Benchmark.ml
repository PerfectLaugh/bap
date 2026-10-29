Bap_script.init ();;

let () =
  let total = ref 0 in
  for n = 1 to 10000000 do
    total := !total + n
  done;
  Printf.printf "%d\n" !total
