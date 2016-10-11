module Curve.Crecip

open FStar.HST
open Hacl.SBuffer
open Curve.Parameters
open Curve.Bigint
open Curve.Bignum

(* Loop for fsquaring, result in the first argument, second is a tmp storage array *)
val loop:
  tmp:bigint -> v:bigint -> ctr:nat -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let rec loop tmp v ctr =
  match ctr with
  | 0 -> ()
  | _ ->
    fsquare tmp v;
    fsquare v tmp;
    loop tmp v (ctr-1)

val assign: bigint -> bigint -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let assign output input = blit input 0ul output 0ul nlength

val crecip':
  output:bigint -> z:bigint -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let crecip' output input = 
  let ftmp = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let ftmp2 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let e2 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let e4 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let e8 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let e16 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let e32 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let e64 = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 5ul in
    
  fsquare ftmp input;  (* 2^1 *)
  fmul ftmp input ftmp; (* 2^2 - 2^0 *)
  assign e2 ftmp;
  fsquare ftmp ftmp;  (* 2^3 - 2^1 *)
  fsquare ftmp ftmp;  (* 2^4 - 2^2 *)
  fmul ftmp ftmp e2;  (* 2^4 - 2^0 *)
  assign e4 ftmp;
  fsquare ftmp ftmp;   (* 2^5 - 2^1 *)
  fsquare ftmp ftmp;   (* 2^6 - 2^2 *)
  fsquare ftmp ftmp;   (* 2^7 - 2^3 *)
  fsquare ftmp ftmp;   (* 2^8 - 2^4 *)
  fmul ftmp ftmp e4;   (* 2^8 - 2^0 *)
  assign e8 ftmp;
  loop tmp ftmp 4;    (* 2^16 - 2^8 *)
  fmul ftmp ftmp e8;   (* 2^16 - 2^0 *)
  assign e16 ftmp;
  loop tmp ftmp 8;   (* 2^32 - 2^16 *)
  fmul ftmp ftmp e16;  (* 2^32 - 2^0 *)
  assign e32 ftmp;
  loop tmp ftmp 16;   (* 2^64 - 2^32 *)
  assign e64 ftmp;
  fmul ftmp ftmp input; (* 2^64 - 2^32 + 2^0 *)
  loop tmp ftmp 96;  (* 2^256 - 2^224 + 2^192 *)

  fmul ftmp2 e64 e32;   (* 2^64 - 2^0 *)
  loop tmp ftmp2 8;  (* 2^80 - 2^16 *)
  fmul ftmp2 ftmp2 e16; (* 2^80 - 2^0 *)
  loop tmp ftmp2 4;   (* 2^88 - 2^8 *)
  fmul ftmp2 ftmp2 e8;  (* 2^88 - 2^0 *)
  loop tmp ftmp2 2;   (* 2^92 - 2^4 *)
  fmul ftmp2 ftmp2 e4;  (* 2^92 - 2^0 *)
  fsquare ftmp2 ftmp2;  (* 2^93 - 2^1 *)
  fsquare ftmp2 ftmp2;  (* 2^94 - 2^2 *)
  fmul ftmp2 ftmp2 e2;  (* 2^94 - 2^0 *)
  fsquare ftmp2 ftmp2;  (* 2^95 - 2^1 *)
  fsquare ftmp2 ftmp2;  (* 2^96 - 2^2 *)
  fmul ftmp2 ftmp2 input; (* 2^96 - 3 *)

  fmul output ftmp2 ftmp
