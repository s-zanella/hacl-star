module Hacl.EC.Curve25519.Parameters

open FStar.Math.Lib
open FStar.Mul
open FStar.Ghost


(* This HAS to go in some more appropriate place *)
assume MaxUInt8 : pow2 8 = 256
assume MaxUInt32: pow2 32 = 4294967296
assume MaxUInt64: pow2 64 > 0xfffffffffffffff
assume MaxUInt128: pow2 128 > pow2 64

inline val prime: erased pos
inline let prime = hide (pow2 255 - 19)
inline let platform_size: pos = 64
inline let platform_wide: pos = 128
inline let norm_length: pos = 5
inline let nlength: x:UInt32.t{UInt32.v x = 5} = 5ul
inline let bytes_length: pos = 32
inline let blength: x:UInt32.t{UInt32.v x = 32} = 32ul
inline let templ: (nat -> Tot pos) = fun i -> 51
inline let a24' = 121665
inline let a24 = 121665uL

(* Required at least for addition *)
inline val parameters_lemma_0: unit -> Lemma (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size)
inline let parameters_lemma_0 () = ()

inline val parameters_lemma_1: unit -> Lemma (platform_wide - 1 >= log_2 norm_length)
inline let parameters_lemma_1 () = ()
