module Hacl.UInt128
(* This module generated automatically using [mk_int.sh] *)

open FStar.UInt128
module U = FStar.UInt128

let n = 128
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [Hacl.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

type t = U.t

let v (x:t) : GTot (FStar.UInt.uint_t n) = U.v x

val add: a:t -> b:t -> Pure t
  (requires (UInt.size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
let add a b = add a b

(* val add_underspec: a:t -> b:t -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun c -> *)
(*     UInt.size (v a + v b) n ==> v a + v b = v c)) *)
(* let add_underspec a b = add_underspec a b *)

val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))
let add_mod a b = add_mod a b

(* Subtraction primitives *)
val sub: a:t -> b:t -> Pure t
  (requires (UInt.size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
let sub a b = sub a b

(* val sub_underspec: a:t -> b:t -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun c -> *)
(*     UInt.size (v a - v b) n ==> v a - v b = v c)) *)
(* let sub_underspec a b = sub_underspec a b *)

val sub_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a - v b) % pow2 n = v c))
let sub_mod a b = sub_mod a b

(* (\* Multiplication primitives *\) *)
(* val mul: a:t -> b:t -> Pure t *)
(*   (requires (UInt.size (v a * v b) n)) *)
(*   (ensures (fun c -> v a * v b = v c)) *)
(* let mul a b = mul a b *)

(* val mul_underspec: a:t -> b:t -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun c -> *)
(*     UInt.size (v a * v b) n ==> v a * v b = v c)) *)
(* let mul_underspec a b = mul_underspec a b *)

(* val mul_mod: a:t -> b:t -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun c -> (v a * v b) % pow2 n = v c))  *)
(* let mul_mod a b = mul_mod a b *)

(* (\* Division primitives *\) *)
(* val div: a:t -> b:t{v b <> 0} -> Pure t *)
(*   (requires (UInt.size (v a / v b) n)) *)
(*   (ensures (fun c -> v b <> 0 ==> v a / v b = v c)) *)
(* let div a b = div a b *)

(* val div_underspec: a:t -> b:t{v b <> 0} -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun c -> *)
(*     (v b <> 0 /\ UInt.size (v a / v b) n) ==> v a / v b = v c)) *)
(* let div_underspec a b = div_underspec a b *)

(* (\* Modulo primitives *\) *)
(* val rem: a:t -> b:t{v b <> 0} -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun c -> *)
(*     v a - ((v a / v b) * v b) = v c)) *)
(* let rem a b = rem a b *)

(* Bitwise operators *)
val logand: t -> t -> Tot t
let logand a b = logand a b
val logxor: t -> t -> Tot t
let logxor a b = logxor a b
val logor: t -> t -> Tot t
let logor a b = logor a b
val lognot: t -> Tot t
let lognot a = lognot a

(* val uint_to_t: x:(UInt.uint_t n) -> Pure t *)
(*   (requires True) *)
(*   (ensures (fun y -> v y = x)) *)
(* let uint_to_t x = uint_to_t x *)

(* Shift operators *)
val shift_right: a:t -> s:FStar.UInt32.t -> Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))))
let shift_right a s = shift_right a s

val shift_left: a:t -> s:FStar.UInt32.t -> Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)))
let shift_left a s = shift_left a s

val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
let eq_mask a b = eq_mask a b
val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
let gte_mask a b = gte_mask a b
val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
let gt_mask a b = lognot (gte_mask b a)
val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
let lt_mask a b = lognot (gte_mask a b)
val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})
let lte_mask a b = lognot (gt_mask a b)

(* Infix notations *)
let op_Plus_Hat = add
(* let op_Plus_Question_Hat = add_underspec *)
let op_Plus_Percent_Hat = add_mod
let op_Subtraction_Hat = sub
(* let op_Subtraction_Question_Hat = sub_underspec *)
let op_Subtraction_Percent_Hat = sub_mod
(* let op_Star_Hat = mul *)
(* let op_Star_Question_Hat = mul_underspec *)
(* let op_Star_Percent_Hat = mul_mod *)
(* let op_Slash_Hat = div *)
(* let op_Percent_Hat = rem *)
let op_Hat_Hat = logxor
let op_Amp_Hat = logand
let op_Bar_Hat = logor
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right

(* (\* To input / output constants *\) *)
(* assume val of_string: string -> Tot t *)

val mul_wide: a:Hacl.UInt64.t -> b:Hacl.UInt64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Hacl.UInt64.v a * Hacl.UInt64.v b))
let mul_wide a b = mul_wide a b
