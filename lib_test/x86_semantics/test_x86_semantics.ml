(* the semantics of the x86 instructions, as bap mc prints it *)

let show = Show.show Show.x86_64

(* Testing SHUFPS
   The control is zero so we take the first word of xmm1 into the two high words
   of the destination and the first word of xmm0 into the two low words *)

let%expect_test "shufps $0x0, %xmm1, %xmm0" =
  show "0f c6 c1 00";
  [%expect
    {|
    shufps $0x0, %xmm1, %xmm0
    {
      YMM0 := high:128[YMM0].31:0[YMM1].31:0[YMM1].31:0[YMM0].31:0[YMM0]
    }
    |}]

(* In this case the control is all ones so we take the last words of xmm1 and xmm0 *)

let%expect_test "shufps $0xff, %xmm1, %xmm0" =
  show "0f c6 c1 ff";
  [%expect
    {|
    shufps $0xff, %xmm1, %xmm0
    {
      YMM0 := high:128[YMM0].127:96[YMM1].127:96[YMM1].127:96[YMM0].127:96[YMM0]
    }
    |}]

(* Now let's reverse the xmm0 register, the control is {0,1,2,3}=0b_00_01_10_11=0x1b *)

let%expect_test "shufps $0x1b, %xmm0, %xmm0" =
  show "0f c6 c0 1b";
  [%expect
    {|
    shufps $0x1b, %xmm0, %xmm0
    {
      YMM0 := high:128[YMM0].31:0[YMM0].63:32[YMM0].95:64[YMM0].127:96[YMM0]
    }
    |}]

(* Let's try the above with a memory argument *)

let%expect_test "shufps $0x1b, 0x10(%rax), %xmm0" =
  show "0f c6 40 10 1b";
  [%expect
    {|
    shufps $0x1b, 0x10(%rax), %xmm0
    {
      #0 := mem[RAX + 0x10, el]:u128
      YMM0 := high:128[YMM0].31:0[#0].63:32[#0].95:64[YMM0].127:96[YMM0]
    }
    |}]

(* Testing PMULDQ
   multiply two registers *)

let%expect_test "pmuldq %xmm1, %xmm0" =
  show "66 0f 38 28 c1";
  [%expect
    {|
    pmuldq %xmm1, %xmm0
    {
      #0 := extend:64[95:64[YMM0]] * extend:64[95:64[YMM1]]
      #1 := extend:64[31:0[YMM0]] * extend:64[31:0[YMM1]]
      YMM0 := high:128[YMM0].#0.#1
    }
    |}]

(* and the same for a memory operand *)

let%expect_test "pmuldq 0x12(%rdi), %xmm0" =
  show "66 0f 38 28 47 12";
  [%expect
    {|
    pmuldq 0x12(%rdi), %xmm0
    {
      #0 := mem[RDI + 0x12, el]:u128
      #1 := extend:64[95:64[YMM0]] * extend:64[95:64[#0]]
      #2 := extend:64[31:0[YMM0]] * extend:64[31:0[#0]]
      YMM0 := high:128[YMM0].#1.#2
    }
    |}]

let%expect_test "pmuludq 0xc(%rdi), %xmm1" =
  show "66 0f f4 4f 0c";
  [%expect
    {|
    pmuludq 0xc(%rdi), %xmm1
    {
      #0 := mem[RDI + 0xC, el]:u128
      #1 := pad:64[95:64[YMM1]] * pad:64[95:64[#0]]
      #2 := pad:64[31:0[YMM1]] * pad:64[31:0[#0]]
      YMM1 := high:128[YMM1].#1.#2
    }
    |}]

let%expect_test "pmuludq %xmm3, %xmm1" =
  show "66 0f f4 cb";
  [%expect
    {|
    pmuludq %xmm3, %xmm1
    {
      #0 := pad:64[95:64[YMM1]] * pad:64[95:64[YMM3]]
      #1 := pad:64[31:0[YMM1]] * pad:64[31:0[YMM3]]
      YMM1 := high:128[YMM1].#0.#1
    }
    |}]

let%expect_test "vpmuludq %xmm4, %xmm3, %xmm1" =
  show "c5 e1 f4 cc";
  [%expect
    {|
    vpmuludq %xmm4, %xmm3, %xmm1
    {
      #0 := pad:64[95:64[YMM3]] * pad:64[95:64[YMM4]]
      #1 := pad:64[31:0[YMM3]] * pad:64[31:0[YMM4]]
      YMM1 := 0.#0.#1
    }
    |}]

let%expect_test "vpmuludq %ymm4, %ymm3, %ymm1" =
  show "c5 e5 f4 cc";
  [%expect
    {|
    vpmuludq %ymm4, %ymm3, %ymm1
    {
      #0 := pad:64[223:192[YMM3]] * pad:64[223:192[YMM4]]
      #1 := pad:64[159:128[YMM3]] * pad:64[159:128[YMM4]]
      #2 := pad:64[95:64[YMM3]] * pad:64[95:64[YMM4]]
      #3 := pad:64[31:0[YMM3]] * pad:64[31:0[YMM4]]
      YMM1 := #0.#1.#2.#3
    }
    |}]

(* Testing xchgb *)

let%expect_test "xchgb %cl, %ah" =
  show "86 e1";
  [%expect
    {|
    xchgb %cl, %ah
    {
      #0 := 15:8[RAX]
      #1 := 7:0[RCX]
      RAX := high:48[RAX].#1.low:8[RAX]
      RCX := high:56[RCX].#0
    }
    |}]

let%expect_test "xchgb %cl, 0x12(%rdi)" =
  show "86 4f 12";
  [%expect
    {|
    xchgb %cl, 0x12(%rdi)
    {
      #0 := RDI + 0x12
      #1 := mem[#0]
      mem := mem with [#0] <- 7:0[RCX]
      RCX := high:56[RCX].#1
    }
    |}]

(* Testing packssdw *)

let%expect_test "packssdw %xmm9, %xmm8" =
  show "66 45 0f 6b c1";
  [%expect
    {|
    packssdw %xmm9, %xmm8
    {
      #0 := 31:0[YMM8]
      #1 :=
        let $0 = #0 ~>> 0xF in
        low:16[if $0 = 0 | ~$0 = 0 then #0 else 0x7FFF + (1 & #0 >> 0x1F)]
      #2 := 63:32[YMM8]
      #3 :=
        let $1 = #2 ~>> 0xF in
        low:16[if $1 = 0 | ~$1 = 0 then #2 else 0x7FFF + (1 & #2 >> 0x1F)]
      #4 := 95:64[YMM8]
      #5 :=
        let $2 = #4 ~>> 0xF in
        low:16[if $2 = 0 | ~$2 = 0 then #4 else 0x7FFF + (1 & #4 >> 0x1F)]
      #6 := 127:96[YMM8]
      #7 :=
        let $3 = #6 ~>> 0xF in
        low:16[if $3 = 0 | ~$3 = 0 then #6 else 0x7FFF + (1 & #6 >> 0x1F)]
      #8 := 31:0[YMM9]
      #9 :=
        let $4 = #8 ~>> 0xF in
        low:16[if $4 = 0 | ~$4 = 0 then #8 else 0x7FFF + (1 & #8 >> 0x1F)]
      #10 := 63:32[YMM9]
      #11 :=
        let $5 = #10 ~>> 0xF in
        low:16[if $5 = 0 | ~$5 = 0 then #10 else 0x7FFF + (1 & #10 >> 0x1F)]
      #12 := 95:64[YMM9]
      #13 :=
        let $6 = #12 ~>> 0xF in
        low:16[if $6 = 0 | ~$6 = 0 then #12 else 0x7FFF + (1 & #12 >> 0x1F)]
      #14 := 127:96[YMM9]
      #15 :=
        let $7 = #14 ~>> 0xF in
        low:16[if $7 = 0 | ~$7 = 0 then #14 else 0x7FFF + (1 & #14 >> 0x1F)]
      YMM8 := high:128[YMM8].#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "packssdw 0x12(%rdi), %xmm0" =
  show "66 0f 6b 47 12";
  [%expect
    {|
    packssdw 0x12(%rdi), %xmm0
    {
      #0 := mem[RDI + 0x12, el]:u128
      #1 := 31:0[YMM0]
      #2 :=
        let $0 = #1 ~>> 0xF in
        low:16[if $0 = 0 | ~$0 = 0 then #1 else 0x7FFF + (1 & #1 >> 0x1F)]
      #3 := 63:32[YMM0]
      #4 :=
        let $1 = #3 ~>> 0xF in
        low:16[if $1 = 0 | ~$1 = 0 then #3 else 0x7FFF + (1 & #3 >> 0x1F)]
      #5 := 95:64[YMM0]
      #6 :=
        let $2 = #5 ~>> 0xF in
        low:16[if $2 = 0 | ~$2 = 0 then #5 else 0x7FFF + (1 & #5 >> 0x1F)]
      #7 := 127:96[YMM0]
      #8 :=
        let $3 = #7 ~>> 0xF in
        low:16[if $3 = 0 | ~$3 = 0 then #7 else 0x7FFF + (1 & #7 >> 0x1F)]
      #9 := 31:0[#0]
      #10 :=
        let $4 = #9 ~>> 0xF in
        low:16[if $4 = 0 | ~$4 = 0 then #9 else 0x7FFF + (1 & #9 >> 0x1F)]
      #11 := 63:32[#0]
      #12 :=
        let $5 = #11 ~>> 0xF in
        low:16[if $5 = 0 | ~$5 = 0 then #11 else 0x7FFF + (1 & #11 >> 0x1F)]
      #13 := 95:64[#0]
      #14 :=
        let $6 = #13 ~>> 0xF in
        low:16[if $6 = 0 | ~$6 = 0 then #13 else 0x7FFF + (1 & #13 >> 0x1F)]
      #15 := 127:96[#0]
      #16 :=
        let $7 = #15 ~>> 0xF in
        low:16[if $7 = 0 | ~$7 = 0 then #15 else 0x7FFF + (1 & #15 >> 0x1F)]
      YMM0 := high:128[YMM0].#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "packsswb %xmm1, %xmm0" =
  show "66 0f 63 c1";
  [%expect
    {|
    packsswb %xmm1, %xmm0
    {
      #0 := 15:0[YMM0]
      #1 :=
        let $0 = #0 ~>> 7 in
        low:8[if $0 = 0 | ~$0 = 0 then #0 else 0x7F + (1 & #0 >> 0xF)]
      #2 := 31:16[YMM0]
      #3 :=
        let $1 = #2 ~>> 7 in
        low:8[if $1 = 0 | ~$1 = 0 then #2 else 0x7F + (1 & #2 >> 0xF)]
      #4 := 47:32[YMM0]
      #5 :=
        let $2 = #4 ~>> 7 in
        low:8[if $2 = 0 | ~$2 = 0 then #4 else 0x7F + (1 & #4 >> 0xF)]
      #6 := 63:48[YMM0]
      #7 :=
        let $3 = #6 ~>> 7 in
        low:8[if $3 = 0 | ~$3 = 0 then #6 else 0x7F + (1 & #6 >> 0xF)]
      #8 := 79:64[YMM0]
      #9 :=
        let $4 = #8 ~>> 7 in
        low:8[if $4 = 0 | ~$4 = 0 then #8 else 0x7F + (1 & #8 >> 0xF)]
      #10 := 95:80[YMM0]
      #11 :=
        let $5 = #10 ~>> 7 in
        low:8[if $5 = 0 | ~$5 = 0 then #10 else 0x7F + (1 & #10 >> 0xF)]
      #12 := 111:96[YMM0]
      #13 :=
        let $6 = #12 ~>> 7 in
        low:8[if $6 = 0 | ~$6 = 0 then #12 else 0x7F + (1 & #12 >> 0xF)]
      #14 := 127:112[YMM0]
      #15 :=
        let $7 = #14 ~>> 7 in
        low:8[if $7 = 0 | ~$7 = 0 then #14 else 0x7F + (1 & #14 >> 0xF)]
      #16 := 15:0[YMM1]
      #17 :=
        let $8 = #16 ~>> 7 in
        low:8[if $8 = 0 | ~$8 = 0 then #16 else 0x7F + (1 & #16 >> 0xF)]
      #18 := 31:16[YMM1]
      #19 :=
        let $9 = #18 ~>> 7 in
        low:8[if $9 = 0 | ~$9 = 0 then #18 else 0x7F + (1 & #18 >> 0xF)]
      #20 := 47:32[YMM1]
      #21 :=
        let $10 = #20 ~>> 7 in
        low:8[if $10 = 0 | ~$10 = 0 then #20 else 0x7F + (1 & #20 >> 0xF)]
      #22 := 63:48[YMM1]
      #23 :=
        let $11 = #22 ~>> 7 in
        low:8[if $11 = 0 | ~$11 = 0 then #22 else 0x7F + (1 & #22 >> 0xF)]
      #24 := 79:64[YMM1]
      #25 :=
        let $12 = #24 ~>> 7 in
        low:8[if $12 = 0 | ~$12 = 0 then #24 else 0x7F + (1 & #24 >> 0xF)]
      #26 := 95:80[YMM1]
      #27 :=
        let $13 = #26 ~>> 7 in
        low:8[if $13 = 0 | ~$13 = 0 then #26 else 0x7F + (1 & #26 >> 0xF)]
      #28 := 111:96[YMM1]
      #29 :=
        let $14 = #28 ~>> 7 in
        low:8[if $14 = 0 | ~$14 = 0 then #28 else 0x7F + (1 & #28 >> 0xF)]
      #30 := 127:112[YMM1]
      #31 :=
        let $15 = #30 ~>> 7 in
        low:8[if $15 = 0 | ~$15 = 0 then #30 else 0x7F + (1 & #30 >> 0xF)]
      YMM0 :=
        high:128[YMM0].#31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "packsswb 0x12(%rax), %xmm0" =
  show "66 0f 63 40 12";
  [%expect
    {|
    packsswb 0x12(%rax), %xmm0
    {
      #0 := mem[RAX + 0x12, el]:u128
      #1 := 15:0[YMM0]
      #2 :=
        let $0 = #1 ~>> 7 in
        low:8[if $0 = 0 | ~$0 = 0 then #1 else 0x7F + (1 & #1 >> 0xF)]
      #3 := 31:16[YMM0]
      #4 :=
        let $1 = #3 ~>> 7 in
        low:8[if $1 = 0 | ~$1 = 0 then #3 else 0x7F + (1 & #3 >> 0xF)]
      #5 := 47:32[YMM0]
      #6 :=
        let $2 = #5 ~>> 7 in
        low:8[if $2 = 0 | ~$2 = 0 then #5 else 0x7F + (1 & #5 >> 0xF)]
      #7 := 63:48[YMM0]
      #8 :=
        let $3 = #7 ~>> 7 in
        low:8[if $3 = 0 | ~$3 = 0 then #7 else 0x7F + (1 & #7 >> 0xF)]
      #9 := 79:64[YMM0]
      #10 :=
        let $4 = #9 ~>> 7 in
        low:8[if $4 = 0 | ~$4 = 0 then #9 else 0x7F + (1 & #9 >> 0xF)]
      #11 := 95:80[YMM0]
      #12 :=
        let $5 = #11 ~>> 7 in
        low:8[if $5 = 0 | ~$5 = 0 then #11 else 0x7F + (1 & #11 >> 0xF)]
      #13 := 111:96[YMM0]
      #14 :=
        let $6 = #13 ~>> 7 in
        low:8[if $6 = 0 | ~$6 = 0 then #13 else 0x7F + (1 & #13 >> 0xF)]
      #15 := 127:112[YMM0]
      #16 :=
        let $7 = #15 ~>> 7 in
        low:8[if $7 = 0 | ~$7 = 0 then #15 else 0x7F + (1 & #15 >> 0xF)]
      #17 := 15:0[#0]
      #18 :=
        let $8 = #17 ~>> 7 in
        low:8[if $8 = 0 | ~$8 = 0 then #17 else 0x7F + (1 & #17 >> 0xF)]
      #19 := 31:16[#0]
      #20 :=
        let $9 = #19 ~>> 7 in
        low:8[if $9 = 0 | ~$9 = 0 then #19 else 0x7F + (1 & #19 >> 0xF)]
      #21 := 47:32[#0]
      #22 :=
        let $10 = #21 ~>> 7 in
        low:8[if $10 = 0 | ~$10 = 0 then #21 else 0x7F + (1 & #21 >> 0xF)]
      #23 := 63:48[#0]
      #24 :=
        let $11 = #23 ~>> 7 in
        low:8[if $11 = 0 | ~$11 = 0 then #23 else 0x7F + (1 & #23 >> 0xF)]
      #25 := 79:64[#0]
      #26 :=
        let $12 = #25 ~>> 7 in
        low:8[if $12 = 0 | ~$12 = 0 then #25 else 0x7F + (1 & #25 >> 0xF)]
      #27 := 95:80[#0]
      #28 :=
        let $13 = #27 ~>> 7 in
        low:8[if $13 = 0 | ~$13 = 0 then #27 else 0x7F + (1 & #27 >> 0xF)]
      #29 := 111:96[#0]
      #30 :=
        let $14 = #29 ~>> 7 in
        low:8[if $14 = 0 | ~$14 = 0 then #29 else 0x7F + (1 & #29 >> 0xF)]
      #31 := 127:112[#0]
      #32 :=
        let $15 = #31 ~>> 7 in
        low:8[if $15 = 0 | ~$15 = 0 then #31 else 0x7F + (1 & #31 >> 0xF)]
      YMM0 :=
        high:128[YMM0].#32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpackssdw %xmm3, %xmm2, %xmm1" =
  show "c5 e9 6b cb";
  [%expect
    {|
    vpackssdw %xmm3, %xmm2, %xmm1
    {
      #0 := 31:0[YMM2]
      #1 :=
        let $0 = #0 ~>> 0xF in
        low:16[if $0 = 0 | ~$0 = 0 then #0 else 0x7FFF + (1 & #0 >> 0x1F)]
      #2 := 63:32[YMM2]
      #3 :=
        let $1 = #2 ~>> 0xF in
        low:16[if $1 = 0 | ~$1 = 0 then #2 else 0x7FFF + (1 & #2 >> 0x1F)]
      #4 := 95:64[YMM2]
      #5 :=
        let $2 = #4 ~>> 0xF in
        low:16[if $2 = 0 | ~$2 = 0 then #4 else 0x7FFF + (1 & #4 >> 0x1F)]
      #6 := 127:96[YMM2]
      #7 :=
        let $3 = #6 ~>> 0xF in
        low:16[if $3 = 0 | ~$3 = 0 then #6 else 0x7FFF + (1 & #6 >> 0x1F)]
      #8 := 31:0[YMM3]
      #9 :=
        let $4 = #8 ~>> 0xF in
        low:16[if $4 = 0 | ~$4 = 0 then #8 else 0x7FFF + (1 & #8 >> 0x1F)]
      #10 := 63:32[YMM3]
      #11 :=
        let $5 = #10 ~>> 0xF in
        low:16[if $5 = 0 | ~$5 = 0 then #10 else 0x7FFF + (1 & #10 >> 0x1F)]
      #12 := 95:64[YMM3]
      #13 :=
        let $6 = #12 ~>> 0xF in
        low:16[if $6 = 0 | ~$6 = 0 then #12 else 0x7FFF + (1 & #12 >> 0x1F)]
      #14 := 127:96[YMM3]
      #15 :=
        let $7 = #14 ~>> 0xF in
        low:16[if $7 = 0 | ~$7 = 0 then #14 else 0x7FFF + (1 & #14 >> 0x1F)]
      YMM1 := high:128[YMM1].#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpackssdw 0x8(%rax), %xmm2, %xmm1" =
  show "c5 e9 6b 48 08";
  [%expect
    {|
    vpackssdw 0x8(%rax), %xmm2, %xmm1
    {
      #0 := mem[RAX + 8, el]:u128
      #1 := 31:0[YMM2]
      #2 :=
        let $0 = #1 ~>> 0xF in
        low:16[if $0 = 0 | ~$0 = 0 then #1 else 0x7FFF + (1 & #1 >> 0x1F)]
      #3 := 63:32[YMM2]
      #4 :=
        let $1 = #3 ~>> 0xF in
        low:16[if $1 = 0 | ~$1 = 0 then #3 else 0x7FFF + (1 & #3 >> 0x1F)]
      #5 := 95:64[YMM2]
      #6 :=
        let $2 = #5 ~>> 0xF in
        low:16[if $2 = 0 | ~$2 = 0 then #5 else 0x7FFF + (1 & #5 >> 0x1F)]
      #7 := 127:96[YMM2]
      #8 :=
        let $3 = #7 ~>> 0xF in
        low:16[if $3 = 0 | ~$3 = 0 then #7 else 0x7FFF + (1 & #7 >> 0x1F)]
      #9 := 31:0[#0]
      #10 :=
        let $4 = #9 ~>> 0xF in
        low:16[if $4 = 0 | ~$4 = 0 then #9 else 0x7FFF + (1 & #9 >> 0x1F)]
      #11 := 63:32[#0]
      #12 :=
        let $5 = #11 ~>> 0xF in
        low:16[if $5 = 0 | ~$5 = 0 then #11 else 0x7FFF + (1 & #11 >> 0x1F)]
      #13 := 95:64[#0]
      #14 :=
        let $6 = #13 ~>> 0xF in
        low:16[if $6 = 0 | ~$6 = 0 then #13 else 0x7FFF + (1 & #13 >> 0x1F)]
      #15 := 127:96[#0]
      #16 :=
        let $7 = #15 ~>> 0xF in
        low:16[if $7 = 0 | ~$7 = 0 then #15 else 0x7FFF + (1 & #15 >> 0x1F)]
      YMM1 := high:128[YMM1].#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpacksswb %xmm3, %xmm2, %xmm1" =
  show "c5 e9 63 cb";
  [%expect
    {|
    vpacksswb %xmm3, %xmm2, %xmm1
    {
      #0 := 15:0[YMM2]
      #1 :=
        let $0 = #0 ~>> 7 in
        low:8[if $0 = 0 | ~$0 = 0 then #0 else 0x7F + (1 & #0 >> 0xF)]
      #2 := 31:16[YMM2]
      #3 :=
        let $1 = #2 ~>> 7 in
        low:8[if $1 = 0 | ~$1 = 0 then #2 else 0x7F + (1 & #2 >> 0xF)]
      #4 := 47:32[YMM2]
      #5 :=
        let $2 = #4 ~>> 7 in
        low:8[if $2 = 0 | ~$2 = 0 then #4 else 0x7F + (1 & #4 >> 0xF)]
      #6 := 63:48[YMM2]
      #7 :=
        let $3 = #6 ~>> 7 in
        low:8[if $3 = 0 | ~$3 = 0 then #6 else 0x7F + (1 & #6 >> 0xF)]
      #8 := 79:64[YMM2]
      #9 :=
        let $4 = #8 ~>> 7 in
        low:8[if $4 = 0 | ~$4 = 0 then #8 else 0x7F + (1 & #8 >> 0xF)]
      #10 := 95:80[YMM2]
      #11 :=
        let $5 = #10 ~>> 7 in
        low:8[if $5 = 0 | ~$5 = 0 then #10 else 0x7F + (1 & #10 >> 0xF)]
      #12 := 111:96[YMM2]
      #13 :=
        let $6 = #12 ~>> 7 in
        low:8[if $6 = 0 | ~$6 = 0 then #12 else 0x7F + (1 & #12 >> 0xF)]
      #14 := 127:112[YMM2]
      #15 :=
        let $7 = #14 ~>> 7 in
        low:8[if $7 = 0 | ~$7 = 0 then #14 else 0x7F + (1 & #14 >> 0xF)]
      #16 := 15:0[YMM3]
      #17 :=
        let $8 = #16 ~>> 7 in
        low:8[if $8 = 0 | ~$8 = 0 then #16 else 0x7F + (1 & #16 >> 0xF)]
      #18 := 31:16[YMM3]
      #19 :=
        let $9 = #18 ~>> 7 in
        low:8[if $9 = 0 | ~$9 = 0 then #18 else 0x7F + (1 & #18 >> 0xF)]
      #20 := 47:32[YMM3]
      #21 :=
        let $10 = #20 ~>> 7 in
        low:8[if $10 = 0 | ~$10 = 0 then #20 else 0x7F + (1 & #20 >> 0xF)]
      #22 := 63:48[YMM3]
      #23 :=
        let $11 = #22 ~>> 7 in
        low:8[if $11 = 0 | ~$11 = 0 then #22 else 0x7F + (1 & #22 >> 0xF)]
      #24 := 79:64[YMM3]
      #25 :=
        let $12 = #24 ~>> 7 in
        low:8[if $12 = 0 | ~$12 = 0 then #24 else 0x7F + (1 & #24 >> 0xF)]
      #26 := 95:80[YMM3]
      #27 :=
        let $13 = #26 ~>> 7 in
        low:8[if $13 = 0 | ~$13 = 0 then #26 else 0x7F + (1 & #26 >> 0xF)]
      #28 := 111:96[YMM3]
      #29 :=
        let $14 = #28 ~>> 7 in
        low:8[if $14 = 0 | ~$14 = 0 then #28 else 0x7F + (1 & #28 >> 0xF)]
      #30 := 127:112[YMM3]
      #31 :=
        let $15 = #30 ~>> 7 in
        low:8[if $15 = 0 | ~$15 = 0 then #30 else 0x7F + (1 & #30 >> 0xF)]
      YMM1 :=
        high:128[YMM1].#31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpacksswb 0x100(%rsi), %xmm2, %xmm1" =
  show "c5 e9 63 8e 00 01 00 00";
  [%expect
    {|
    vpacksswb 0x100(%rsi), %xmm2, %xmm1
    {
      #0 := mem[RSI + 0x100, el]:u128
      #1 := 15:0[YMM2]
      #2 :=
        let $0 = #1 ~>> 7 in
        low:8[if $0 = 0 | ~$0 = 0 then #1 else 0x7F + (1 & #1 >> 0xF)]
      #3 := 31:16[YMM2]
      #4 :=
        let $1 = #3 ~>> 7 in
        low:8[if $1 = 0 | ~$1 = 0 then #3 else 0x7F + (1 & #3 >> 0xF)]
      #5 := 47:32[YMM2]
      #6 :=
        let $2 = #5 ~>> 7 in
        low:8[if $2 = 0 | ~$2 = 0 then #5 else 0x7F + (1 & #5 >> 0xF)]
      #7 := 63:48[YMM2]
      #8 :=
        let $3 = #7 ~>> 7 in
        low:8[if $3 = 0 | ~$3 = 0 then #7 else 0x7F + (1 & #7 >> 0xF)]
      #9 := 79:64[YMM2]
      #10 :=
        let $4 = #9 ~>> 7 in
        low:8[if $4 = 0 | ~$4 = 0 then #9 else 0x7F + (1 & #9 >> 0xF)]
      #11 := 95:80[YMM2]
      #12 :=
        let $5 = #11 ~>> 7 in
        low:8[if $5 = 0 | ~$5 = 0 then #11 else 0x7F + (1 & #11 >> 0xF)]
      #13 := 111:96[YMM2]
      #14 :=
        let $6 = #13 ~>> 7 in
        low:8[if $6 = 0 | ~$6 = 0 then #13 else 0x7F + (1 & #13 >> 0xF)]
      #15 := 127:112[YMM2]
      #16 :=
        let $7 = #15 ~>> 7 in
        low:8[if $7 = 0 | ~$7 = 0 then #15 else 0x7F + (1 & #15 >> 0xF)]
      #17 := 15:0[#0]
      #18 :=
        let $8 = #17 ~>> 7 in
        low:8[if $8 = 0 | ~$8 = 0 then #17 else 0x7F + (1 & #17 >> 0xF)]
      #19 := 31:16[#0]
      #20 :=
        let $9 = #19 ~>> 7 in
        low:8[if $9 = 0 | ~$9 = 0 then #19 else 0x7F + (1 & #19 >> 0xF)]
      #21 := 47:32[#0]
      #22 :=
        let $10 = #21 ~>> 7 in
        low:8[if $10 = 0 | ~$10 = 0 then #21 else 0x7F + (1 & #21 >> 0xF)]
      #23 := 63:48[#0]
      #24 :=
        let $11 = #23 ~>> 7 in
        low:8[if $11 = 0 | ~$11 = 0 then #23 else 0x7F + (1 & #23 >> 0xF)]
      #25 := 79:64[#0]
      #26 :=
        let $12 = #25 ~>> 7 in
        low:8[if $12 = 0 | ~$12 = 0 then #25 else 0x7F + (1 & #25 >> 0xF)]
      #27 := 95:80[#0]
      #28 :=
        let $13 = #27 ~>> 7 in
        low:8[if $13 = 0 | ~$13 = 0 then #27 else 0x7F + (1 & #27 >> 0xF)]
      #29 := 111:96[#0]
      #30 :=
        let $14 = #29 ~>> 7 in
        low:8[if $14 = 0 | ~$14 = 0 then #29 else 0x7F + (1 & #29 >> 0xF)]
      #31 := 127:112[#0]
      #32 :=
        let $15 = #31 ~>> 7 in
        low:8[if $15 = 0 | ~$15 = 0 then #31 else 0x7F + (1 & #31 >> 0xF)]
      YMM1 :=
        high:128[YMM1].#32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpackssdw %ymm3, %ymm2, %ymm1" =
  show "c5 ed 6b cb";
  [%expect
    {|
    vpackssdw %ymm3, %ymm2, %ymm1
    {
      #0 := 31:0[YMM2]
      #1 :=
        let $0 = #0 ~>> 0xF in
        low:16[if $0 = 0 | ~$0 = 0 then #0 else 0x7FFF + (1 & #0 >> 0x1F)]
      #2 := 63:32[YMM2]
      #3 :=
        let $1 = #2 ~>> 0xF in
        low:16[if $1 = 0 | ~$1 = 0 then #2 else 0x7FFF + (1 & #2 >> 0x1F)]
      #4 := 95:64[YMM2]
      #5 :=
        let $2 = #4 ~>> 0xF in
        low:16[if $2 = 0 | ~$2 = 0 then #4 else 0x7FFF + (1 & #4 >> 0x1F)]
      #6 := 127:96[YMM2]
      #7 :=
        let $3 = #6 ~>> 0xF in
        low:16[if $3 = 0 | ~$3 = 0 then #6 else 0x7FFF + (1 & #6 >> 0x1F)]
      #8 := 31:0[YMM3]
      #9 :=
        let $4 = #8 ~>> 0xF in
        low:16[if $4 = 0 | ~$4 = 0 then #8 else 0x7FFF + (1 & #8 >> 0x1F)]
      #10 := 63:32[YMM3]
      #11 :=
        let $5 = #10 ~>> 0xF in
        low:16[if $5 = 0 | ~$5 = 0 then #10 else 0x7FFF + (1 & #10 >> 0x1F)]
      #12 := 95:64[YMM3]
      #13 :=
        let $6 = #12 ~>> 0xF in
        low:16[if $6 = 0 | ~$6 = 0 then #12 else 0x7FFF + (1 & #12 >> 0x1F)]
      #14 := 127:96[YMM3]
      #15 :=
        let $7 = #14 ~>> 0xF in
        low:16[if $7 = 0 | ~$7 = 0 then #14 else 0x7FFF + (1 & #14 >> 0x1F)]
      #16 := 159:128[YMM2]
      #17 :=
        let $8 = #16 ~>> 0xF in
        low:16[if $8 = 0 | ~$8 = 0 then #16 else 0x7FFF + (1 & #16 >> 0x1F)]
      #18 := 191:160[YMM2]
      #19 :=
        let $9 = #18 ~>> 0xF in
        low:16[if $9 = 0 | ~$9 = 0 then #18 else 0x7FFF + (1 & #18 >> 0x1F)]
      #20 := 223:192[YMM2]
      #21 :=
        let $10 = #20 ~>> 0xF in
        low:16[if $10 = 0 | ~$10 = 0 then #20 else 0x7FFF + (1 & #20 >> 0x1F)]
      #22 := 255:224[YMM2]
      #23 :=
        let $11 = #22 ~>> 0xF in
        low:16[if $11 = 0 | ~$11 = 0 then #22 else 0x7FFF + (1 & #22 >> 0x1F)]
      #24 := 159:128[YMM3]
      #25 :=
        let $12 = #24 ~>> 0xF in
        low:16[if $12 = 0 | ~$12 = 0 then #24 else 0x7FFF + (1 & #24 >> 0x1F)]
      #26 := 191:160[YMM3]
      #27 :=
        let $13 = #26 ~>> 0xF in
        low:16[if $13 = 0 | ~$13 = 0 then #26 else 0x7FFF + (1 & #26 >> 0x1F)]
      #28 := 223:192[YMM3]
      #29 :=
        let $14 = #28 ~>> 0xF in
        low:16[if $14 = 0 | ~$14 = 0 then #28 else 0x7FFF + (1 & #28 >> 0x1F)]
      #30 := 255:224[YMM3]
      #31 :=
        let $15 = #30 ~>> 0xF in
        low:16[if $15 = 0 | ~$15 = 0 then #30 else 0x7FFF + (1 & #30 >> 0x1F)]
      YMM1 :=
        #31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpackssdw 0x4(%rdx), %ymm2, %ymm1" =
  show "c5 ed 6b 4a 04";
  [%expect
    {|
    vpackssdw 0x4(%rdx), %ymm2, %ymm1
    {
      #0 := mem[RDX + 4, el]:u256
      #1 := 31:0[YMM2]
      #2 :=
        let $0 = #1 ~>> 0xF in
        low:16[if $0 = 0 | ~$0 = 0 then #1 else 0x7FFF + (1 & #1 >> 0x1F)]
      #3 := 63:32[YMM2]
      #4 :=
        let $1 = #3 ~>> 0xF in
        low:16[if $1 = 0 | ~$1 = 0 then #3 else 0x7FFF + (1 & #3 >> 0x1F)]
      #5 := 95:64[YMM2]
      #6 :=
        let $2 = #5 ~>> 0xF in
        low:16[if $2 = 0 | ~$2 = 0 then #5 else 0x7FFF + (1 & #5 >> 0x1F)]
      #7 := 127:96[YMM2]
      #8 :=
        let $3 = #7 ~>> 0xF in
        low:16[if $3 = 0 | ~$3 = 0 then #7 else 0x7FFF + (1 & #7 >> 0x1F)]
      #9 := 31:0[#0]
      #10 :=
        let $4 = #9 ~>> 0xF in
        low:16[if $4 = 0 | ~$4 = 0 then #9 else 0x7FFF + (1 & #9 >> 0x1F)]
      #11 := 63:32[#0]
      #12 :=
        let $5 = #11 ~>> 0xF in
        low:16[if $5 = 0 | ~$5 = 0 then #11 else 0x7FFF + (1 & #11 >> 0x1F)]
      #13 := 95:64[#0]
      #14 :=
        let $6 = #13 ~>> 0xF in
        low:16[if $6 = 0 | ~$6 = 0 then #13 else 0x7FFF + (1 & #13 >> 0x1F)]
      #15 := 127:96[#0]
      #16 :=
        let $7 = #15 ~>> 0xF in
        low:16[if $7 = 0 | ~$7 = 0 then #15 else 0x7FFF + (1 & #15 >> 0x1F)]
      #17 := 159:128[YMM2]
      #18 :=
        let $8 = #17 ~>> 0xF in
        low:16[if $8 = 0 | ~$8 = 0 then #17 else 0x7FFF + (1 & #17 >> 0x1F)]
      #19 := 191:160[YMM2]
      #20 :=
        let $9 = #19 ~>> 0xF in
        low:16[if $9 = 0 | ~$9 = 0 then #19 else 0x7FFF + (1 & #19 >> 0x1F)]
      #21 := 223:192[YMM2]
      #22 :=
        let $10 = #21 ~>> 0xF in
        low:16[if $10 = 0 | ~$10 = 0 then #21 else 0x7FFF + (1 & #21 >> 0x1F)]
      #23 := 255:224[YMM2]
      #24 :=
        let $11 = #23 ~>> 0xF in
        low:16[if $11 = 0 | ~$11 = 0 then #23 else 0x7FFF + (1 & #23 >> 0x1F)]
      #25 := 159:128[#0]
      #26 :=
        let $12 = #25 ~>> 0xF in
        low:16[if $12 = 0 | ~$12 = 0 then #25 else 0x7FFF + (1 & #25 >> 0x1F)]
      #27 := 191:160[#0]
      #28 :=
        let $13 = #27 ~>> 0xF in
        low:16[if $13 = 0 | ~$13 = 0 then #27 else 0x7FFF + (1 & #27 >> 0x1F)]
      #29 := 223:192[#0]
      #30 :=
        let $14 = #29 ~>> 0xF in
        low:16[if $14 = 0 | ~$14 = 0 then #29 else 0x7FFF + (1 & #29 >> 0x1F)]
      #31 := 255:224[#0]
      #32 :=
        let $15 = #31 ~>> 0xF in
        low:16[if $15 = 0 | ~$15 = 0 then #31 else 0x7FFF + (1 & #31 >> 0x1F)]
      YMM1 :=
        #32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpacksswb %ymm3, %ymm2, %ymm1" =
  show "c5 ed 63 cb";
  [%expect
    {|
    vpacksswb %ymm3, %ymm2, %ymm1
    {
      #0 := 15:0[YMM2]
      #1 :=
        let $0 = #0 ~>> 7 in
        low:8[if $0 = 0 | ~$0 = 0 then #0 else 0x7F + (1 & #0 >> 0xF)]
      #2 := 31:16[YMM2]
      #3 :=
        let $1 = #2 ~>> 7 in
        low:8[if $1 = 0 | ~$1 = 0 then #2 else 0x7F + (1 & #2 >> 0xF)]
      #4 := 47:32[YMM2]
      #5 :=
        let $2 = #4 ~>> 7 in
        low:8[if $2 = 0 | ~$2 = 0 then #4 else 0x7F + (1 & #4 >> 0xF)]
      #6 := 63:48[YMM2]
      #7 :=
        let $3 = #6 ~>> 7 in
        low:8[if $3 = 0 | ~$3 = 0 then #6 else 0x7F + (1 & #6 >> 0xF)]
      #8 := 79:64[YMM2]
      #9 :=
        let $4 = #8 ~>> 7 in
        low:8[if $4 = 0 | ~$4 = 0 then #8 else 0x7F + (1 & #8 >> 0xF)]
      #10 := 95:80[YMM2]
      #11 :=
        let $5 = #10 ~>> 7 in
        low:8[if $5 = 0 | ~$5 = 0 then #10 else 0x7F + (1 & #10 >> 0xF)]
      #12 := 111:96[YMM2]
      #13 :=
        let $6 = #12 ~>> 7 in
        low:8[if $6 = 0 | ~$6 = 0 then #12 else 0x7F + (1 & #12 >> 0xF)]
      #14 := 127:112[YMM2]
      #15 :=
        let $7 = #14 ~>> 7 in
        low:8[if $7 = 0 | ~$7 = 0 then #14 else 0x7F + (1 & #14 >> 0xF)]
      #16 := 15:0[YMM3]
      #17 :=
        let $8 = #16 ~>> 7 in
        low:8[if $8 = 0 | ~$8 = 0 then #16 else 0x7F + (1 & #16 >> 0xF)]
      #18 := 31:16[YMM3]
      #19 :=
        let $9 = #18 ~>> 7 in
        low:8[if $9 = 0 | ~$9 = 0 then #18 else 0x7F + (1 & #18 >> 0xF)]
      #20 := 47:32[YMM3]
      #21 :=
        let $10 = #20 ~>> 7 in
        low:8[if $10 = 0 | ~$10 = 0 then #20 else 0x7F + (1 & #20 >> 0xF)]
      #22 := 63:48[YMM3]
      #23 :=
        let $11 = #22 ~>> 7 in
        low:8[if $11 = 0 | ~$11 = 0 then #22 else 0x7F + (1 & #22 >> 0xF)]
      #24 := 79:64[YMM3]
      #25 :=
        let $12 = #24 ~>> 7 in
        low:8[if $12 = 0 | ~$12 = 0 then #24 else 0x7F + (1 & #24 >> 0xF)]
      #26 := 95:80[YMM3]
      #27 :=
        let $13 = #26 ~>> 7 in
        low:8[if $13 = 0 | ~$13 = 0 then #26 else 0x7F + (1 & #26 >> 0xF)]
      #28 := 111:96[YMM3]
      #29 :=
        let $14 = #28 ~>> 7 in
        low:8[if $14 = 0 | ~$14 = 0 then #28 else 0x7F + (1 & #28 >> 0xF)]
      #30 := 127:112[YMM3]
      #31 :=
        let $15 = #30 ~>> 7 in
        low:8[if $15 = 0 | ~$15 = 0 then #30 else 0x7F + (1 & #30 >> 0xF)]
      #32 := 143:128[YMM2]
      #33 :=
        let $16 = #32 ~>> 7 in
        low:8[if $16 = 0 | ~$16 = 0 then #32 else 0x7F + (1 & #32 >> 0xF)]
      #34 := 159:144[YMM2]
      #35 :=
        let $17 = #34 ~>> 7 in
        low:8[if $17 = 0 | ~$17 = 0 then #34 else 0x7F + (1 & #34 >> 0xF)]
      #36 := 175:160[YMM2]
      #37 :=
        let $18 = #36 ~>> 7 in
        low:8[if $18 = 0 | ~$18 = 0 then #36 else 0x7F + (1 & #36 >> 0xF)]
      #38 := 191:176[YMM2]
      #39 :=
        let $19 = #38 ~>> 7 in
        low:8[if $19 = 0 | ~$19 = 0 then #38 else 0x7F + (1 & #38 >> 0xF)]
      #40 := 207:192[YMM2]
      #41 :=
        let $20 = #40 ~>> 7 in
        low:8[if $20 = 0 | ~$20 = 0 then #40 else 0x7F + (1 & #40 >> 0xF)]
      #42 := 223:208[YMM2]
      #43 :=
        let $21 = #42 ~>> 7 in
        low:8[if $21 = 0 | ~$21 = 0 then #42 else 0x7F + (1 & #42 >> 0xF)]
      #44 := 239:224[YMM2]
      #45 :=
        let $22 = #44 ~>> 7 in
        low:8[if $22 = 0 | ~$22 = 0 then #44 else 0x7F + (1 & #44 >> 0xF)]
      #46 := 255:240[YMM2]
      #47 :=
        let $23 = #46 ~>> 7 in
        low:8[if $23 = 0 | ~$23 = 0 then #46 else 0x7F + (1 & #46 >> 0xF)]
      #48 := 143:128[YMM3]
      #49 :=
        let $24 = #48 ~>> 7 in
        low:8[if $24 = 0 | ~$24 = 0 then #48 else 0x7F + (1 & #48 >> 0xF)]
      #50 := 159:144[YMM3]
      #51 :=
        let $25 = #50 ~>> 7 in
        low:8[if $25 = 0 | ~$25 = 0 then #50 else 0x7F + (1 & #50 >> 0xF)]
      #52 := 175:160[YMM3]
      #53 :=
        let $26 = #52 ~>> 7 in
        low:8[if $26 = 0 | ~$26 = 0 then #52 else 0x7F + (1 & #52 >> 0xF)]
      #54 := 191:176[YMM3]
      #55 :=
        let $27 = #54 ~>> 7 in
        low:8[if $27 = 0 | ~$27 = 0 then #54 else 0x7F + (1 & #54 >> 0xF)]
      #56 := 207:192[YMM3]
      #57 :=
        let $28 = #56 ~>> 7 in
        low:8[if $28 = 0 | ~$28 = 0 then #56 else 0x7F + (1 & #56 >> 0xF)]
      #58 := 223:208[YMM3]
      #59 :=
        let $29 = #58 ~>> 7 in
        low:8[if $29 = 0 | ~$29 = 0 then #58 else 0x7F + (1 & #58 >> 0xF)]
      #60 := 239:224[YMM3]
      #61 :=
        let $30 = #60 ~>> 7 in
        low:8[if $30 = 0 | ~$30 = 0 then #60 else 0x7F + (1 & #60 >> 0xF)]
      #62 := 255:240[YMM3]
      #63 :=
        let $31 = #62 ~>> 7 in
        low:8[if $31 = 0 | ~$31 = 0 then #62 else 0x7F + (1 & #62 >> 0xF)]
      YMM1 :=
        #63.#61.#59.#57.#55.#53.#51.#49.#47.#45.#43.#41.#39.#37.#35.#33.#31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpacksswb (%rcx), %ymm2, %ymm1" =
  show "c5 ed 63 09";
  [%expect
    {|
    vpacksswb (%rcx), %ymm2, %ymm1
    {
      #0 := mem[RCX, el]:u256
      #1 := 15:0[YMM2]
      #2 :=
        let $0 = #1 ~>> 7 in
        low:8[if $0 = 0 | ~$0 = 0 then #1 else 0x7F + (1 & #1 >> 0xF)]
      #3 := 31:16[YMM2]
      #4 :=
        let $1 = #3 ~>> 7 in
        low:8[if $1 = 0 | ~$1 = 0 then #3 else 0x7F + (1 & #3 >> 0xF)]
      #5 := 47:32[YMM2]
      #6 :=
        let $2 = #5 ~>> 7 in
        low:8[if $2 = 0 | ~$2 = 0 then #5 else 0x7F + (1 & #5 >> 0xF)]
      #7 := 63:48[YMM2]
      #8 :=
        let $3 = #7 ~>> 7 in
        low:8[if $3 = 0 | ~$3 = 0 then #7 else 0x7F + (1 & #7 >> 0xF)]
      #9 := 79:64[YMM2]
      #10 :=
        let $4 = #9 ~>> 7 in
        low:8[if $4 = 0 | ~$4 = 0 then #9 else 0x7F + (1 & #9 >> 0xF)]
      #11 := 95:80[YMM2]
      #12 :=
        let $5 = #11 ~>> 7 in
        low:8[if $5 = 0 | ~$5 = 0 then #11 else 0x7F + (1 & #11 >> 0xF)]
      #13 := 111:96[YMM2]
      #14 :=
        let $6 = #13 ~>> 7 in
        low:8[if $6 = 0 | ~$6 = 0 then #13 else 0x7F + (1 & #13 >> 0xF)]
      #15 := 127:112[YMM2]
      #16 :=
        let $7 = #15 ~>> 7 in
        low:8[if $7 = 0 | ~$7 = 0 then #15 else 0x7F + (1 & #15 >> 0xF)]
      #17 := 15:0[#0]
      #18 :=
        let $8 = #17 ~>> 7 in
        low:8[if $8 = 0 | ~$8 = 0 then #17 else 0x7F + (1 & #17 >> 0xF)]
      #19 := 31:16[#0]
      #20 :=
        let $9 = #19 ~>> 7 in
        low:8[if $9 = 0 | ~$9 = 0 then #19 else 0x7F + (1 & #19 >> 0xF)]
      #21 := 47:32[#0]
      #22 :=
        let $10 = #21 ~>> 7 in
        low:8[if $10 = 0 | ~$10 = 0 then #21 else 0x7F + (1 & #21 >> 0xF)]
      #23 := 63:48[#0]
      #24 :=
        let $11 = #23 ~>> 7 in
        low:8[if $11 = 0 | ~$11 = 0 then #23 else 0x7F + (1 & #23 >> 0xF)]
      #25 := 79:64[#0]
      #26 :=
        let $12 = #25 ~>> 7 in
        low:8[if $12 = 0 | ~$12 = 0 then #25 else 0x7F + (1 & #25 >> 0xF)]
      #27 := 95:80[#0]
      #28 :=
        let $13 = #27 ~>> 7 in
        low:8[if $13 = 0 | ~$13 = 0 then #27 else 0x7F + (1 & #27 >> 0xF)]
      #29 := 111:96[#0]
      #30 :=
        let $14 = #29 ~>> 7 in
        low:8[if $14 = 0 | ~$14 = 0 then #29 else 0x7F + (1 & #29 >> 0xF)]
      #31 := 127:112[#0]
      #32 :=
        let $15 = #31 ~>> 7 in
        low:8[if $15 = 0 | ~$15 = 0 then #31 else 0x7F + (1 & #31 >> 0xF)]
      YMM1 :=
        #32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "packusdw %xmm2, %xmm1" =
  show "66 0f 38 2b ca";
  [%expect
    {|
    packusdw %xmm2, %xmm1
    {
      #0 := 31:0[YMM1]
      #1 := low:16[if #0 ~>> 0x10 = 0 then #0 else 0xFFFF + (1 & #0 >> 0x1F)]
      #2 := 63:32[YMM1]
      #3 := low:16[if #2 ~>> 0x10 = 0 then #2 else 0xFFFF + (1 & #2 >> 0x1F)]
      #4 := 95:64[YMM1]
      #5 := low:16[if #4 ~>> 0x10 = 0 then #4 else 0xFFFF + (1 & #4 >> 0x1F)]
      #6 := 127:96[YMM1]
      #7 := low:16[if #6 ~>> 0x10 = 0 then #6 else 0xFFFF + (1 & #6 >> 0x1F)]
      #8 := 31:0[YMM2]
      #9 := low:16[if #8 ~>> 0x10 = 0 then #8 else 0xFFFF + (1 & #8 >> 0x1F)]
      #10 := 63:32[YMM2]
      #11 :=
        low:16[if #10 ~>> 0x10 = 0 then #10 else 0xFFFF + (1 & #10 >> 0x1F)]
      #12 := 95:64[YMM2]
      #13 :=
        low:16[if #12 ~>> 0x10 = 0 then #12 else 0xFFFF + (1 & #12 >> 0x1F)]
      #14 := 127:96[YMM2]
      #15 :=
        low:16[if #14 ~>> 0x10 = 0 then #14 else 0xFFFF + (1 & #14 >> 0x1F)]
      YMM1 := high:128[YMM1].#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "packusdw (%rdi), %xmm1" =
  show "66 0f 38 2b 0f";
  [%expect
    {|
    packusdw (%rdi), %xmm1
    {
      #0 := mem[RDI, el]:u128
      #1 := 31:0[YMM1]
      #2 := low:16[if #1 ~>> 0x10 = 0 then #1 else 0xFFFF + (1 & #1 >> 0x1F)]
      #3 := 63:32[YMM1]
      #4 := low:16[if #3 ~>> 0x10 = 0 then #3 else 0xFFFF + (1 & #3 >> 0x1F)]
      #5 := 95:64[YMM1]
      #6 := low:16[if #5 ~>> 0x10 = 0 then #5 else 0xFFFF + (1 & #5 >> 0x1F)]
      #7 := 127:96[YMM1]
      #8 := low:16[if #7 ~>> 0x10 = 0 then #7 else 0xFFFF + (1 & #7 >> 0x1F)]
      #9 := 31:0[#0]
      #10 :=
        low:16[if #9 ~>> 0x10 = 0 then #9 else 0xFFFF + (1 & #9 >> 0x1F)]
      #11 := 63:32[#0]
      #12 :=
        low:16[if #11 ~>> 0x10 = 0 then #11 else 0xFFFF + (1 & #11 >> 0x1F)]
      #13 := 95:64[#0]
      #14 :=
        low:16[if #13 ~>> 0x10 = 0 then #13 else 0xFFFF + (1 & #13 >> 0x1F)]
      #15 := 127:96[#0]
      #16 :=
        low:16[if #15 ~>> 0x10 = 0 then #15 else 0xFFFF + (1 & #15 >> 0x1F)]
      YMM1 := high:128[YMM1].#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpackusdw %xmm3, %xmm2, %xmm1" =
  show "c4 e2 69 2b cb";
  [%expect
    {|
    vpackusdw %xmm3, %xmm2, %xmm1
    {
      #0 := 31:0[YMM2]
      #1 := low:16[if #0 ~>> 0x10 = 0 then #0 else 0xFFFF + (1 & #0 >> 0x1F)]
      #2 := 63:32[YMM2]
      #3 := low:16[if #2 ~>> 0x10 = 0 then #2 else 0xFFFF + (1 & #2 >> 0x1F)]
      #4 := 95:64[YMM2]
      #5 := low:16[if #4 ~>> 0x10 = 0 then #4 else 0xFFFF + (1 & #4 >> 0x1F)]
      #6 := 127:96[YMM2]
      #7 := low:16[if #6 ~>> 0x10 = 0 then #6 else 0xFFFF + (1 & #6 >> 0x1F)]
      #8 := 31:0[YMM3]
      #9 := low:16[if #8 ~>> 0x10 = 0 then #8 else 0xFFFF + (1 & #8 >> 0x1F)]
      #10 := 63:32[YMM3]
      #11 :=
        low:16[if #10 ~>> 0x10 = 0 then #10 else 0xFFFF + (1 & #10 >> 0x1F)]
      #12 := 95:64[YMM3]
      #13 :=
        low:16[if #12 ~>> 0x10 = 0 then #12 else 0xFFFF + (1 & #12 >> 0x1F)]
      #14 := 127:96[YMM3]
      #15 :=
        low:16[if #14 ~>> 0x10 = 0 then #14 else 0xFFFF + (1 & #14 >> 0x1F)]
      YMM1 := high:128[YMM1].#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpackusdw %ymm3, %ymm2, %ymm1" =
  show "c4 e2 6d 2b cb";
  [%expect
    {|
    vpackusdw %ymm3, %ymm2, %ymm1
    {
      #0 := 31:0[YMM2]
      #1 := low:16[if #0 ~>> 0x10 = 0 then #0 else 0xFFFF + (1 & #0 >> 0x1F)]
      #2 := 63:32[YMM2]
      #3 := low:16[if #2 ~>> 0x10 = 0 then #2 else 0xFFFF + (1 & #2 >> 0x1F)]
      #4 := 95:64[YMM2]
      #5 := low:16[if #4 ~>> 0x10 = 0 then #4 else 0xFFFF + (1 & #4 >> 0x1F)]
      #6 := 127:96[YMM2]
      #7 := low:16[if #6 ~>> 0x10 = 0 then #6 else 0xFFFF + (1 & #6 >> 0x1F)]
      #8 := 31:0[YMM3]
      #9 := low:16[if #8 ~>> 0x10 = 0 then #8 else 0xFFFF + (1 & #8 >> 0x1F)]
      #10 := 63:32[YMM3]
      #11 :=
        low:16[if #10 ~>> 0x10 = 0 then #10 else 0xFFFF + (1 & #10 >> 0x1F)]
      #12 := 95:64[YMM3]
      #13 :=
        low:16[if #12 ~>> 0x10 = 0 then #12 else 0xFFFF + (1 & #12 >> 0x1F)]
      #14 := 127:96[YMM3]
      #15 :=
        low:16[if #14 ~>> 0x10 = 0 then #14 else 0xFFFF + (1 & #14 >> 0x1F)]
      #16 := 159:128[YMM2]
      #17 :=
        low:16[if #16 ~>> 0x10 = 0 then #16 else 0xFFFF + (1 & #16 >> 0x1F)]
      #18 := 191:160[YMM2]
      #19 :=
        low:16[if #18 ~>> 0x10 = 0 then #18 else 0xFFFF + (1 & #18 >> 0x1F)]
      #20 := 223:192[YMM2]
      #21 :=
        low:16[if #20 ~>> 0x10 = 0 then #20 else 0xFFFF + (1 & #20 >> 0x1F)]
      #22 := 255:224[YMM2]
      #23 :=
        low:16[if #22 ~>> 0x10 = 0 then #22 else 0xFFFF + (1 & #22 >> 0x1F)]
      #24 := 159:128[YMM3]
      #25 :=
        low:16[if #24 ~>> 0x10 = 0 then #24 else 0xFFFF + (1 & #24 >> 0x1F)]
      #26 := 191:160[YMM3]
      #27 :=
        low:16[if #26 ~>> 0x10 = 0 then #26 else 0xFFFF + (1 & #26 >> 0x1F)]
      #28 := 223:192[YMM3]
      #29 :=
        low:16[if #28 ~>> 0x10 = 0 then #28 else 0xFFFF + (1 & #28 >> 0x1F)]
      #30 := 255:224[YMM3]
      #31 :=
        low:16[if #30 ~>> 0x10 = 0 then #30 else 0xFFFF + (1 & #30 >> 0x1F)]
      YMM1 :=
        #31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpackusdw 0x10(%rax), %ymm2, %ymm1" =
  show "c4 e2 6d 2b 48 10";
  [%expect
    {|
    vpackusdw 0x10(%rax), %ymm2, %ymm1
    {
      #0 := mem[RAX + 0x10, el]:u256
      #1 := 31:0[YMM2]
      #2 := low:16[if #1 ~>> 0x10 = 0 then #1 else 0xFFFF + (1 & #1 >> 0x1F)]
      #3 := 63:32[YMM2]
      #4 := low:16[if #3 ~>> 0x10 = 0 then #3 else 0xFFFF + (1 & #3 >> 0x1F)]
      #5 := 95:64[YMM2]
      #6 := low:16[if #5 ~>> 0x10 = 0 then #5 else 0xFFFF + (1 & #5 >> 0x1F)]
      #7 := 127:96[YMM2]
      #8 := low:16[if #7 ~>> 0x10 = 0 then #7 else 0xFFFF + (1 & #7 >> 0x1F)]
      #9 := 31:0[#0]
      #10 :=
        low:16[if #9 ~>> 0x10 = 0 then #9 else 0xFFFF + (1 & #9 >> 0x1F)]
      #11 := 63:32[#0]
      #12 :=
        low:16[if #11 ~>> 0x10 = 0 then #11 else 0xFFFF + (1 & #11 >> 0x1F)]
      #13 := 95:64[#0]
      #14 :=
        low:16[if #13 ~>> 0x10 = 0 then #13 else 0xFFFF + (1 & #13 >> 0x1F)]
      #15 := 127:96[#0]
      #16 :=
        low:16[if #15 ~>> 0x10 = 0 then #15 else 0xFFFF + (1 & #15 >> 0x1F)]
      #17 := 159:128[YMM2]
      #18 :=
        low:16[if #17 ~>> 0x10 = 0 then #17 else 0xFFFF + (1 & #17 >> 0x1F)]
      #19 := 191:160[YMM2]
      #20 :=
        low:16[if #19 ~>> 0x10 = 0 then #19 else 0xFFFF + (1 & #19 >> 0x1F)]
      #21 := 223:192[YMM2]
      #22 :=
        low:16[if #21 ~>> 0x10 = 0 then #21 else 0xFFFF + (1 & #21 >> 0x1F)]
      #23 := 255:224[YMM2]
      #24 :=
        low:16[if #23 ~>> 0x10 = 0 then #23 else 0xFFFF + (1 & #23 >> 0x1F)]
      #25 := 159:128[#0]
      #26 :=
        low:16[if #25 ~>> 0x10 = 0 then #25 else 0xFFFF + (1 & #25 >> 0x1F)]
      #27 := 191:160[#0]
      #28 :=
        low:16[if #27 ~>> 0x10 = 0 then #27 else 0xFFFF + (1 & #27 >> 0x1F)]
      #29 := 223:192[#0]
      #30 :=
        low:16[if #29 ~>> 0x10 = 0 then #29 else 0xFFFF + (1 & #29 >> 0x1F)]
      #31 := 255:224[#0]
      #32 :=
        low:16[if #31 ~>> 0x10 = 0 then #31 else 0xFFFF + (1 & #31 >> 0x1F)]
      YMM1 :=
        #32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "packuswb %xmm2, %xmm1" =
  show "66 0f 67 ca";
  [%expect
    {|
    packuswb %xmm2, %xmm1
    {
      #0 := 15:0[YMM1]
      #1 := low:8[if #0 ~>> 8 = 0 then #0 else 0xFF + (1 & #0 >> 0xF)]
      #2 := 31:16[YMM1]
      #3 := low:8[if #2 ~>> 8 = 0 then #2 else 0xFF + (1 & #2 >> 0xF)]
      #4 := 47:32[YMM1]
      #5 := low:8[if #4 ~>> 8 = 0 then #4 else 0xFF + (1 & #4 >> 0xF)]
      #6 := 63:48[YMM1]
      #7 := low:8[if #6 ~>> 8 = 0 then #6 else 0xFF + (1 & #6 >> 0xF)]
      #8 := 79:64[YMM1]
      #9 := low:8[if #8 ~>> 8 = 0 then #8 else 0xFF + (1 & #8 >> 0xF)]
      #10 := 95:80[YMM1]
      #11 := low:8[if #10 ~>> 8 = 0 then #10 else 0xFF + (1 & #10 >> 0xF)]
      #12 := 111:96[YMM1]
      #13 := low:8[if #12 ~>> 8 = 0 then #12 else 0xFF + (1 & #12 >> 0xF)]
      #14 := 127:112[YMM1]
      #15 := low:8[if #14 ~>> 8 = 0 then #14 else 0xFF + (1 & #14 >> 0xF)]
      #16 := 15:0[YMM2]
      #17 := low:8[if #16 ~>> 8 = 0 then #16 else 0xFF + (1 & #16 >> 0xF)]
      #18 := 31:16[YMM2]
      #19 := low:8[if #18 ~>> 8 = 0 then #18 else 0xFF + (1 & #18 >> 0xF)]
      #20 := 47:32[YMM2]
      #21 := low:8[if #20 ~>> 8 = 0 then #20 else 0xFF + (1 & #20 >> 0xF)]
      #22 := 63:48[YMM2]
      #23 := low:8[if #22 ~>> 8 = 0 then #22 else 0xFF + (1 & #22 >> 0xF)]
      #24 := 79:64[YMM2]
      #25 := low:8[if #24 ~>> 8 = 0 then #24 else 0xFF + (1 & #24 >> 0xF)]
      #26 := 95:80[YMM2]
      #27 := low:8[if #26 ~>> 8 = 0 then #26 else 0xFF + (1 & #26 >> 0xF)]
      #28 := 111:96[YMM2]
      #29 := low:8[if #28 ~>> 8 = 0 then #28 else 0xFF + (1 & #28 >> 0xF)]
      #30 := 127:112[YMM2]
      #31 := low:8[if #30 ~>> 8 = 0 then #30 else 0xFF + (1 & #30 >> 0xF)]
      YMM1 :=
        high:128[YMM1].#31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "packuswb (%rdi), %xmm1" =
  show "66 0f 67 0f";
  [%expect
    {|
    packuswb (%rdi), %xmm1
    {
      #0 := mem[RDI, el]:u128
      #1 := 15:0[YMM1]
      #2 := low:8[if #1 ~>> 8 = 0 then #1 else 0xFF + (1 & #1 >> 0xF)]
      #3 := 31:16[YMM1]
      #4 := low:8[if #3 ~>> 8 = 0 then #3 else 0xFF + (1 & #3 >> 0xF)]
      #5 := 47:32[YMM1]
      #6 := low:8[if #5 ~>> 8 = 0 then #5 else 0xFF + (1 & #5 >> 0xF)]
      #7 := 63:48[YMM1]
      #8 := low:8[if #7 ~>> 8 = 0 then #7 else 0xFF + (1 & #7 >> 0xF)]
      #9 := 79:64[YMM1]
      #10 := low:8[if #9 ~>> 8 = 0 then #9 else 0xFF + (1 & #9 >> 0xF)]
      #11 := 95:80[YMM1]
      #12 := low:8[if #11 ~>> 8 = 0 then #11 else 0xFF + (1 & #11 >> 0xF)]
      #13 := 111:96[YMM1]
      #14 := low:8[if #13 ~>> 8 = 0 then #13 else 0xFF + (1 & #13 >> 0xF)]
      #15 := 127:112[YMM1]
      #16 := low:8[if #15 ~>> 8 = 0 then #15 else 0xFF + (1 & #15 >> 0xF)]
      #17 := 15:0[#0]
      #18 := low:8[if #17 ~>> 8 = 0 then #17 else 0xFF + (1 & #17 >> 0xF)]
      #19 := 31:16[#0]
      #20 := low:8[if #19 ~>> 8 = 0 then #19 else 0xFF + (1 & #19 >> 0xF)]
      #21 := 47:32[#0]
      #22 := low:8[if #21 ~>> 8 = 0 then #21 else 0xFF + (1 & #21 >> 0xF)]
      #23 := 63:48[#0]
      #24 := low:8[if #23 ~>> 8 = 0 then #23 else 0xFF + (1 & #23 >> 0xF)]
      #25 := 79:64[#0]
      #26 := low:8[if #25 ~>> 8 = 0 then #25 else 0xFF + (1 & #25 >> 0xF)]
      #27 := 95:80[#0]
      #28 := low:8[if #27 ~>> 8 = 0 then #27 else 0xFF + (1 & #27 >> 0xF)]
      #29 := 111:96[#0]
      #30 := low:8[if #29 ~>> 8 = 0 then #29 else 0xFF + (1 & #29 >> 0xF)]
      #31 := 127:112[#0]
      #32 := low:8[if #31 ~>> 8 = 0 then #31 else 0xFF + (1 & #31 >> 0xF)]
      YMM1 :=
        high:128[YMM1].#32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpackuswb %xmm2, %xmm1, %xmm0" =
  show "c5 f1 67 c2";
  [%expect
    {|
    vpackuswb %xmm2, %xmm1, %xmm0
    {
      #0 := 15:0[YMM1]
      #1 := low:8[if #0 ~>> 8 = 0 then #0 else 0xFF + (1 & #0 >> 0xF)]
      #2 := 31:16[YMM1]
      #3 := low:8[if #2 ~>> 8 = 0 then #2 else 0xFF + (1 & #2 >> 0xF)]
      #4 := 47:32[YMM1]
      #5 := low:8[if #4 ~>> 8 = 0 then #4 else 0xFF + (1 & #4 >> 0xF)]
      #6 := 63:48[YMM1]
      #7 := low:8[if #6 ~>> 8 = 0 then #6 else 0xFF + (1 & #6 >> 0xF)]
      #8 := 79:64[YMM1]
      #9 := low:8[if #8 ~>> 8 = 0 then #8 else 0xFF + (1 & #8 >> 0xF)]
      #10 := 95:80[YMM1]
      #11 := low:8[if #10 ~>> 8 = 0 then #10 else 0xFF + (1 & #10 >> 0xF)]
      #12 := 111:96[YMM1]
      #13 := low:8[if #12 ~>> 8 = 0 then #12 else 0xFF + (1 & #12 >> 0xF)]
      #14 := 127:112[YMM1]
      #15 := low:8[if #14 ~>> 8 = 0 then #14 else 0xFF + (1 & #14 >> 0xF)]
      #16 := 15:0[YMM2]
      #17 := low:8[if #16 ~>> 8 = 0 then #16 else 0xFF + (1 & #16 >> 0xF)]
      #18 := 31:16[YMM2]
      #19 := low:8[if #18 ~>> 8 = 0 then #18 else 0xFF + (1 & #18 >> 0xF)]
      #20 := 47:32[YMM2]
      #21 := low:8[if #20 ~>> 8 = 0 then #20 else 0xFF + (1 & #20 >> 0xF)]
      #22 := 63:48[YMM2]
      #23 := low:8[if #22 ~>> 8 = 0 then #22 else 0xFF + (1 & #22 >> 0xF)]
      #24 := 79:64[YMM2]
      #25 := low:8[if #24 ~>> 8 = 0 then #24 else 0xFF + (1 & #24 >> 0xF)]
      #26 := 95:80[YMM2]
      #27 := low:8[if #26 ~>> 8 = 0 then #26 else 0xFF + (1 & #26 >> 0xF)]
      #28 := 111:96[YMM2]
      #29 := low:8[if #28 ~>> 8 = 0 then #28 else 0xFF + (1 & #28 >> 0xF)]
      #30 := 127:112[YMM2]
      #31 := low:8[if #30 ~>> 8 = 0 then #30 else 0xFF + (1 & #30 >> 0xF)]
      YMM0 :=
        high:128[YMM0].#31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpackuswb (%rax), %xmm1, %xmm0" =
  show "c5 f1 67 00";
  [%expect
    {|
    vpackuswb (%rax), %xmm1, %xmm0
    {
      #0 := mem[RAX, el]:u128
      #1 := 15:0[YMM1]
      #2 := low:8[if #1 ~>> 8 = 0 then #1 else 0xFF + (1 & #1 >> 0xF)]
      #3 := 31:16[YMM1]
      #4 := low:8[if #3 ~>> 8 = 0 then #3 else 0xFF + (1 & #3 >> 0xF)]
      #5 := 47:32[YMM1]
      #6 := low:8[if #5 ~>> 8 = 0 then #5 else 0xFF + (1 & #5 >> 0xF)]
      #7 := 63:48[YMM1]
      #8 := low:8[if #7 ~>> 8 = 0 then #7 else 0xFF + (1 & #7 >> 0xF)]
      #9 := 79:64[YMM1]
      #10 := low:8[if #9 ~>> 8 = 0 then #9 else 0xFF + (1 & #9 >> 0xF)]
      #11 := 95:80[YMM1]
      #12 := low:8[if #11 ~>> 8 = 0 then #11 else 0xFF + (1 & #11 >> 0xF)]
      #13 := 111:96[YMM1]
      #14 := low:8[if #13 ~>> 8 = 0 then #13 else 0xFF + (1 & #13 >> 0xF)]
      #15 := 127:112[YMM1]
      #16 := low:8[if #15 ~>> 8 = 0 then #15 else 0xFF + (1 & #15 >> 0xF)]
      #17 := 15:0[#0]
      #18 := low:8[if #17 ~>> 8 = 0 then #17 else 0xFF + (1 & #17 >> 0xF)]
      #19 := 31:16[#0]
      #20 := low:8[if #19 ~>> 8 = 0 then #19 else 0xFF + (1 & #19 >> 0xF)]
      #21 := 47:32[#0]
      #22 := low:8[if #21 ~>> 8 = 0 then #21 else 0xFF + (1 & #21 >> 0xF)]
      #23 := 63:48[#0]
      #24 := low:8[if #23 ~>> 8 = 0 then #23 else 0xFF + (1 & #23 >> 0xF)]
      #25 := 79:64[#0]
      #26 := low:8[if #25 ~>> 8 = 0 then #25 else 0xFF + (1 & #25 >> 0xF)]
      #27 := 95:80[#0]
      #28 := low:8[if #27 ~>> 8 = 0 then #27 else 0xFF + (1 & #27 >> 0xF)]
      #29 := 111:96[#0]
      #30 := low:8[if #29 ~>> 8 = 0 then #29 else 0xFF + (1 & #29 >> 0xF)]
      #31 := 127:112[#0]
      #32 := low:8[if #31 ~>> 8 = 0 then #31 else 0xFF + (1 & #31 >> 0xF)]
      YMM0 :=
        high:128[YMM0].#32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vpackuswb %ymm3, %ymm1, %ymm0" =
  show "c5 f5 67 c3";
  [%expect
    {|
    vpackuswb %ymm3, %ymm1, %ymm0
    {
      #0 := 15:0[YMM1]
      #1 := low:8[if #0 ~>> 8 = 0 then #0 else 0xFF + (1 & #0 >> 0xF)]
      #2 := 31:16[YMM1]
      #3 := low:8[if #2 ~>> 8 = 0 then #2 else 0xFF + (1 & #2 >> 0xF)]
      #4 := 47:32[YMM1]
      #5 := low:8[if #4 ~>> 8 = 0 then #4 else 0xFF + (1 & #4 >> 0xF)]
      #6 := 63:48[YMM1]
      #7 := low:8[if #6 ~>> 8 = 0 then #6 else 0xFF + (1 & #6 >> 0xF)]
      #8 := 79:64[YMM1]
      #9 := low:8[if #8 ~>> 8 = 0 then #8 else 0xFF + (1 & #8 >> 0xF)]
      #10 := 95:80[YMM1]
      #11 := low:8[if #10 ~>> 8 = 0 then #10 else 0xFF + (1 & #10 >> 0xF)]
      #12 := 111:96[YMM1]
      #13 := low:8[if #12 ~>> 8 = 0 then #12 else 0xFF + (1 & #12 >> 0xF)]
      #14 := 127:112[YMM1]
      #15 := low:8[if #14 ~>> 8 = 0 then #14 else 0xFF + (1 & #14 >> 0xF)]
      #16 := 15:0[YMM3]
      #17 := low:8[if #16 ~>> 8 = 0 then #16 else 0xFF + (1 & #16 >> 0xF)]
      #18 := 31:16[YMM3]
      #19 := low:8[if #18 ~>> 8 = 0 then #18 else 0xFF + (1 & #18 >> 0xF)]
      #20 := 47:32[YMM3]
      #21 := low:8[if #20 ~>> 8 = 0 then #20 else 0xFF + (1 & #20 >> 0xF)]
      #22 := 63:48[YMM3]
      #23 := low:8[if #22 ~>> 8 = 0 then #22 else 0xFF + (1 & #22 >> 0xF)]
      #24 := 79:64[YMM3]
      #25 := low:8[if #24 ~>> 8 = 0 then #24 else 0xFF + (1 & #24 >> 0xF)]
      #26 := 95:80[YMM3]
      #27 := low:8[if #26 ~>> 8 = 0 then #26 else 0xFF + (1 & #26 >> 0xF)]
      #28 := 111:96[YMM3]
      #29 := low:8[if #28 ~>> 8 = 0 then #28 else 0xFF + (1 & #28 >> 0xF)]
      #30 := 127:112[YMM3]
      #31 := low:8[if #30 ~>> 8 = 0 then #30 else 0xFF + (1 & #30 >> 0xF)]
      #32 := 143:128[YMM1]
      #33 := low:8[if #32 ~>> 8 = 0 then #32 else 0xFF + (1 & #32 >> 0xF)]
      #34 := 159:144[YMM1]
      #35 := low:8[if #34 ~>> 8 = 0 then #34 else 0xFF + (1 & #34 >> 0xF)]
      #36 := 175:160[YMM1]
      #37 := low:8[if #36 ~>> 8 = 0 then #36 else 0xFF + (1 & #36 >> 0xF)]
      #38 := 191:176[YMM1]
      #39 := low:8[if #38 ~>> 8 = 0 then #38 else 0xFF + (1 & #38 >> 0xF)]
      #40 := 207:192[YMM1]
      #41 := low:8[if #40 ~>> 8 = 0 then #40 else 0xFF + (1 & #40 >> 0xF)]
      #42 := 223:208[YMM1]
      #43 := low:8[if #42 ~>> 8 = 0 then #42 else 0xFF + (1 & #42 >> 0xF)]
      #44 := 239:224[YMM1]
      #45 := low:8[if #44 ~>> 8 = 0 then #44 else 0xFF + (1 & #44 >> 0xF)]
      #46 := 255:240[YMM1]
      #47 := low:8[if #46 ~>> 8 = 0 then #46 else 0xFF + (1 & #46 >> 0xF)]
      #48 := 143:128[YMM3]
      #49 := low:8[if #48 ~>> 8 = 0 then #48 else 0xFF + (1 & #48 >> 0xF)]
      #50 := 159:144[YMM3]
      #51 := low:8[if #50 ~>> 8 = 0 then #50 else 0xFF + (1 & #50 >> 0xF)]
      #52 := 175:160[YMM3]
      #53 := low:8[if #52 ~>> 8 = 0 then #52 else 0xFF + (1 & #52 >> 0xF)]
      #54 := 191:176[YMM3]
      #55 := low:8[if #54 ~>> 8 = 0 then #54 else 0xFF + (1 & #54 >> 0xF)]
      #56 := 207:192[YMM3]
      #57 := low:8[if #56 ~>> 8 = 0 then #56 else 0xFF + (1 & #56 >> 0xF)]
      #58 := 223:208[YMM3]
      #59 := low:8[if #58 ~>> 8 = 0 then #58 else 0xFF + (1 & #58 >> 0xF)]
      #60 := 239:224[YMM3]
      #61 := low:8[if #60 ~>> 8 = 0 then #60 else 0xFF + (1 & #60 >> 0xF)]
      #62 := 255:240[YMM3]
      #63 := low:8[if #62 ~>> 8 = 0 then #62 else 0xFF + (1 & #62 >> 0xF)]
      YMM0 :=
        #63.#61.#59.#57.#55.#53.#51.#49.#47.#45.#43.#41.#39.#37.#35.#33.#31.#29.#27.#25.#23.#21.#19.#17.#15.#13.#11.#9.#7.#5.#3.#1
    }
    |}]

let%expect_test "vpackuswb 0x20(%rdi), %ymm1, %ymm0" =
  show "c5 f5 67 47 20";
  [%expect
    {|
    vpackuswb 0x20(%rdi), %ymm1, %ymm0
    {
      #0 := mem[RDI + 0x20, el]:u256
      #1 := 15:0[YMM1]
      #2 := low:8[if #1 ~>> 8 = 0 then #1 else 0xFF + (1 & #1 >> 0xF)]
      #3 := 31:16[YMM1]
      #4 := low:8[if #3 ~>> 8 = 0 then #3 else 0xFF + (1 & #3 >> 0xF)]
      #5 := 47:32[YMM1]
      #6 := low:8[if #5 ~>> 8 = 0 then #5 else 0xFF + (1 & #5 >> 0xF)]
      #7 := 63:48[YMM1]
      #8 := low:8[if #7 ~>> 8 = 0 then #7 else 0xFF + (1 & #7 >> 0xF)]
      #9 := 79:64[YMM1]
      #10 := low:8[if #9 ~>> 8 = 0 then #9 else 0xFF + (1 & #9 >> 0xF)]
      #11 := 95:80[YMM1]
      #12 := low:8[if #11 ~>> 8 = 0 then #11 else 0xFF + (1 & #11 >> 0xF)]
      #13 := 111:96[YMM1]
      #14 := low:8[if #13 ~>> 8 = 0 then #13 else 0xFF + (1 & #13 >> 0xF)]
      #15 := 127:112[YMM1]
      #16 := low:8[if #15 ~>> 8 = 0 then #15 else 0xFF + (1 & #15 >> 0xF)]
      #17 := 15:0[#0]
      #18 := low:8[if #17 ~>> 8 = 0 then #17 else 0xFF + (1 & #17 >> 0xF)]
      #19 := 31:16[#0]
      #20 := low:8[if #19 ~>> 8 = 0 then #19 else 0xFF + (1 & #19 >> 0xF)]
      #21 := 47:32[#0]
      #22 := low:8[if #21 ~>> 8 = 0 then #21 else 0xFF + (1 & #21 >> 0xF)]
      #23 := 63:48[#0]
      #24 := low:8[if #23 ~>> 8 = 0 then #23 else 0xFF + (1 & #23 >> 0xF)]
      #25 := 79:64[#0]
      #26 := low:8[if #25 ~>> 8 = 0 then #25 else 0xFF + (1 & #25 >> 0xF)]
      #27 := 95:80[#0]
      #28 := low:8[if #27 ~>> 8 = 0 then #27 else 0xFF + (1 & #27 >> 0xF)]
      #29 := 111:96[#0]
      #30 := low:8[if #29 ~>> 8 = 0 then #29 else 0xFF + (1 & #29 >> 0xF)]
      #31 := 127:112[#0]
      #32 := low:8[if #31 ~>> 8 = 0 then #31 else 0xFF + (1 & #31 >> 0xF)]
      YMM0 :=
        #32.#30.#28.#26.#24.#22.#20.#18.#16.#14.#12.#10.#8.#6.#4.#2
    }
    |}]

let%expect_test "vzeroupper" =
  show "c5 f8 77";
  [%expect
    {|
    vzeroupper
    {
      YMM0 := 0.low:128[YMM0]
      YMM1 := 0.low:128[YMM1]
      YMM2 := 0.low:128[YMM2]
      YMM3 := 0.low:128[YMM3]
      YMM4 := 0.low:128[YMM4]
      YMM5 := 0.low:128[YMM5]
      YMM6 := 0.low:128[YMM6]
      YMM7 := 0.low:128[YMM7]
      YMM8 := 0.low:128[YMM8]
      YMM9 := 0.low:128[YMM9]
      YMM10 := 0.low:128[YMM10]
      YMM11 := 0.low:128[YMM11]
      YMM12 := 0.low:128[YMM12]
      YMM13 := 0.low:128[YMM13]
      YMM14 := 0.low:128[YMM14]
      YMM15 := 0.low:128[YMM15]
    }
    |}]

let%expect_test "movntdq %xmm0, 0x10(%rdi)" =
  show "66 0f e7 47 10";
  [%expect
    {|
    movntdq %xmm0, 0x10(%rdi)
    {
      mem := mem with [RDI + 0x10, el]:u128 <- 127:0[YMM0]
    }
    |}]

let%expect_test "vmovntdq %xmm0, 0x10(%rdi)" =
  show "c5 f9 e7 47 10";
  [%expect
    {|
    vmovntdq %xmm0, 0x10(%rdi)
    {
      mem := mem with [RDI + 0x10, el]:u128 <- 127:0[YMM0]
    }
    |}]

let%expect_test "vmovntdq %ymm0, 0x10(%rdi)" =
  show "c5 fd e7 47 10";
  [%expect
    {|
    vmovntdq %ymm0, 0x10(%rdi)
    {
      mem := mem with [RDI + 0x10, el]:u256 <- YMM0
    }
    |}]

(* [v]andp{d,s}: *)

let%expect_test "andps %xmm2, %xmm1" =
  show "0f 54 ca";
  [%expect
    {|
    andps %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "andpd %xmm2, %xmm1" =
  show "66 0f 54 ca";
  [%expect
    {|
    andpd %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "vandps %xmm2, %xmm1, %xmm0" =
  show "c5 f0 54 c2";
  [%expect
    {|
    vandps %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "vandpd %xmm2, %xmm1, %xmm0" =
  show "c5 f1 54 c2";
  [%expect
    {|
    vandpd %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "andps 0x2a(%rsi), %xmm1" =
  show "0f 54 4e 2a";
  [%expect
    {|
    andps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "andps 0x2a(%rsi), %xmm1" =
  show "0f 54 4e 2a";
  [%expect
    {|
    andps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "andpd 0x2a(%rsi), %xmm1" =
  show "66 0f 54 4e 2a";
  [%expect
    {|
    andpd 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vandps 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f0 54 46 2a";
  [%expect
    {|
    vandps 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vandpd 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f1 54 46 2a";
  [%expect
    {|
    vandpd 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vandps 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f4 54 46 2a";
  [%expect
    {|
    vandps 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := YMM1 & mem[RSI + 0x2A, el]:u256
    }
    |}]

let%expect_test "vandpd 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f5 54 46 2a";
  [%expect
    {|
    vandpd 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := YMM1 & mem[RSI + 0x2A, el]:u256
    }
    |}]

(* [v]orp{d,s}: *)

let%expect_test "orps %xmm2, %xmm1" =
  show "0f 56 ca";
  [%expect
    {|
    orps %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] | 127:0[YMM2]
    }
    |}]

let%expect_test "orpd %xmm2, %xmm1" =
  show "66 0f 56 ca";
  [%expect
    {|
    orpd %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] | 127:0[YMM2]
    }
    |}]

let%expect_test "vorps %xmm2, %xmm1, %xmm0" =
  show "c5 f0 56 c2";
  [%expect
    {|
    vorps %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] | 127:0[YMM2]
    }
    |}]

let%expect_test "vorpd %xmm2, %xmm1, %xmm0" =
  show "c5 f1 56 c2";
  [%expect
    {|
    vorpd %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] | 127:0[YMM2]
    }
    |}]

let%expect_test "orps 0x2a(%rsi), %xmm1" =
  show "0f 56 4e 2a";
  [%expect
    {|
    orps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] | mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "orps 0x2a(%rsi), %xmm1" =
  show "0f 56 4e 2a";
  [%expect
    {|
    orps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] | mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "orpd 0x2a(%rsi), %xmm1" =
  show "66 0f 56 4e 2a";
  [%expect
    {|
    orpd 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] | mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vorps 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f0 56 46 2a";
  [%expect
    {|
    vorps 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] | mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vorpd 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f1 56 46 2a";
  [%expect
    {|
    vorpd 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] | mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vorps 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f4 56 46 2a";
  [%expect
    {|
    vorps 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := YMM1 | mem[RSI + 0x2A, el]:u256
    }
    |}]

let%expect_test "vorpd 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f5 56 46 2a";
  [%expect
    {|
    vorpd 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := YMM1 | mem[RSI + 0x2A, el]:u256
    }
    |}]

(* [v]xorp{d,s}: *)

let%expect_test "xorps %xmm2, %xmm1" =
  show "0f 57 ca";
  [%expect
    {|
    xorps %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] ^ 127:0[YMM2]
    }
    |}]

let%expect_test "xorpd %xmm2, %xmm1" =
  show "66 0f 57 ca";
  [%expect
    {|
    xorpd %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] ^ 127:0[YMM2]
    }
    |}]

let%expect_test "vxorps %xmm2, %xmm1, %xmm0" =
  show "c5 f0 57 c2";
  [%expect
    {|
    vxorps %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] ^ 127:0[YMM2]
    }
    |}]

let%expect_test "vxorpd %xmm2, %xmm1, %xmm0" =
  show "c5 f1 57 c2";
  [%expect
    {|
    vxorpd %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] ^ 127:0[YMM2]
    }
    |}]

let%expect_test "xorps 0x2a(%rsi), %xmm1" =
  show "0f 57 4e 2a";
  [%expect
    {|
    xorps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] ^ mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "xorps 0x2a(%rsi), %xmm1" =
  show "0f 57 4e 2a";
  [%expect
    {|
    xorps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] ^ mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "xorpd 0x2a(%rsi), %xmm1" =
  show "66 0f 57 4e 2a";
  [%expect
    {|
    xorpd 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].127:0[YMM1] ^ mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vxorps 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f0 57 46 2a";
  [%expect
    {|
    vxorps 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] ^ mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vxorpd 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f1 57 46 2a";
  [%expect
    {|
    vxorpd 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.127:0[YMM1] ^ mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vxorps 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f4 57 46 2a";
  [%expect
    {|
    vxorps 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := YMM1 ^ mem[RSI + 0x2A, el]:u256
    }
    |}]

let%expect_test "vxorpd 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f5 57 46 2a";
  [%expect
    {|
    vxorpd 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := YMM1 ^ mem[RSI + 0x2A, el]:u256
    }
    |}]

(* [v]andnp{d,s}: *)

let%expect_test "andnps %xmm2, %xmm1" =
  show "0f 55 ca";
  [%expect
    {|
    andnps %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].~127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "andnpd %xmm2, %xmm1" =
  show "66 0f 55 ca";
  [%expect
    {|
    andnpd %xmm2, %xmm1
    {
      YMM1 := high:128[YMM1].~127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "vandnps %xmm2, %xmm1, %xmm0" =
  show "c5 f0 55 c2";
  [%expect
    {|
    vandnps %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.~127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "vandnpd %xmm2, %xmm1, %xmm0" =
  show "c5 f1 55 c2";
  [%expect
    {|
    vandnpd %xmm2, %xmm1, %xmm0
    {
      YMM0 := 0.~127:0[YMM1] & 127:0[YMM2]
    }
    |}]

let%expect_test "andnps 0x2a(%rsi), %xmm1" =
  show "0f 55 4e 2a";
  [%expect
    {|
    andnps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].~127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "andnps 0x2a(%rsi), %xmm1" =
  show "0f 55 4e 2a";
  [%expect
    {|
    andnps 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].~127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "andnpd 0x2a(%rsi), %xmm1" =
  show "66 0f 55 4e 2a";
  [%expect
    {|
    andnpd 0x2a(%rsi), %xmm1
    {
      YMM1 := high:128[YMM1].~127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vandnps 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f0 55 46 2a";
  [%expect
    {|
    vandnps 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.~127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vandnpd 0x2a(%rsi), %xmm1, %xmm0" =
  show "c5 f1 55 46 2a";
  [%expect
    {|
    vandnpd 0x2a(%rsi), %xmm1, %xmm0
    {
      YMM0 := 0.~127:0[YMM1] & mem[RSI + 0x2A, el]:u128
    }
    |}]

let%expect_test "vandnps 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f4 55 46 2a";
  [%expect
    {|
    vandnps 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := ~YMM1 & mem[RSI + 0x2A, el]:u256
    }
    |}]

let%expect_test "vandnpd 0x2a(%rsi), %ymm1, %ymm0" =
  show "c5 f5 55 46 2a";
  [%expect
    {|
    vandnpd 0x2a(%rsi), %ymm1, %ymm0
    {
      YMM0 := ~YMM1 & mem[RSI + 0x2A, el]:u256
    }
    |}]
