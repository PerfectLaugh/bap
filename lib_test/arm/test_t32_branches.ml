(* the T32 branches, whose targets depend on the alignment of their
   addresses, which the generated tests don't change *)

(* the instructions at 0x10002, which is not word-aligned *)
let t32 = Arm_tests_helpers.t32_at 0x10002

let suite =
  OUnit2.( >::: ) "T32 branches"
    [
      (* blx switches to A32, so its target is relative to Align(PC, 4),
         0x10004, and the return address keeps the T32 state *)
      Lifter_test.case t32 "blx .+0x3a" "00 f0 1c e8"
        [ ([], [ ("PC", "0x1003c"); ("LR", "0x10007") ]) ];
    ]
