module Curve.Parameters

open Math.Lib
open FStar.Mul
open FStar.Ghost

val prime: erased pos
let prime = hide (pow2 448 - pow2 224 - 1)
let platform_size: pos = 64
let platform_wide: pos = 128
let norm_length: pos = 8
let nlength: x:UInt32.t{UInt32.v x = 8} = 8ul
let bytes_length: pos = 56
let blength: x:UInt32.t{UInt32.v x = 56} = 56ul
let templ: (nat -> Tot pos) = fun i -> 56
let a24' = 39081
let a24 = 39081uL

(* Required at least for addition *)
val parameters_lemma_0: unit -> Lemma (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size)
let parameters_lemma_0 () = ()

val parameters_lemma_1: unit -> Lemma (platform_wide - 1 >= log_2 norm_length)
let parameters_lemma_1 () = ()
