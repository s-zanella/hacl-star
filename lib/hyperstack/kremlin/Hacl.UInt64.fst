module Hacl.UInt64
(* This module generated automatically using [mk_int.sh] *)

open FStar.UInt64
module U = FStar.UInt64

let n = 64
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [Hacl.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

type t = U.t

let v (x:t) : GTot (FStar.UInt.uint_t n) = U.v x

inline_for_extraction val add: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})
inline_for_extraction let add a b = add a b

inline_for_extraction val add_mod: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})
inline_for_extraction let add_mod a b = add_mod a b

(* Subtraction primitives *)
inline_for_extraction val sub: a:t -> b:t{(UInt.size (v a - v b) n)} -> Tot (c:t{v a - v b = v c})
inline_for_extraction let sub a b = sub a b

inline_for_extraction val sub_mod: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})
inline_for_extraction let sub_mod a b = sub_mod a b

(* Multiplication primitives *)
inline_for_extraction val mul: a:t -> b:t{UInt.size (v a * v b) n} -> Tot (c:t{v a * v b = v c})
inline_for_extraction let mul a b = mul a b

inline_for_extraction val mul_mod: a:t -> b:t -> Tot (c:t{(v a * v b) % pow2 n = v c})
inline_for_extraction let mul_mod a b = mul_mod a b

(* Bitwise operators *)
inline_for_extraction val logand: t -> t -> Tot t
inline_for_extraction let logand a b = logand a b
inline_for_extraction val logxor: t -> t -> Tot t
inline_for_extraction let logxor a b = logxor a b
inline_for_extraction val logor: t -> t -> Tot t
inline_for_extraction let logor a b = logor a b
inline_for_extraction val lognot: t -> Tot t
inline_for_extraction let lognot a = lognot a

(* Shift operators *)
inline_for_extraction val shift_right: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction let shift_right a s = shift_right a s

inline_for_extraction val shift_left: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})
inline_for_extraction let shift_left a s = shift_left a s

inline_for_extraction val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
inline_for_extraction let eq_mask a b = eq_mask a b
inline_for_extraction val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
inline_for_extraction let gte_mask a b = gte_mask a b
inline_for_extraction val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
inline_for_extraction let gt_mask a b = lognot (gte_mask b a)
inline_for_extraction val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
inline_for_extraction let lt_mask a b = lognot (gte_mask a b)
inline_for_extraction val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})
inline_for_extraction let lte_mask a b = lognot (gt_mask a b)


(* Infix notations *)

inline_for_extraction val op_Plus_Hat: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})
inline_for_extraction let op_Plus_Hat a b = add a b

inline_for_extraction val op_Plus_Percent_Hat: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})
inline_for_extraction let op_Plus_Percent_Hat a b = add_mod a b

inline_for_extraction val op_Subtraction_Hat: a:t -> b:t{(UInt.size (v a - v b) n)} -> Tot (c:t{v a - v b = v c})
inline_for_extraction let op_Subtraction_Hat a b = sub a b

inline_for_extraction val op_Subtraction_Percent_Hat: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})
inline_for_extraction let op_Subtraction_Percent_Hat a b = sub_mod a b

inline_for_extraction val op_Star_Hat: a:t -> b:t{UInt.size (v a * v b) n} -> Tot (c:t{v a * v b = v c})
inline_for_extraction let op_Star_Hat a b = mul a b

inline_for_extraction val op_Star_Percent_Hat: a:t -> b:t -> Tot (c:t{(v a * v b) % pow2 n = v c})
inline_for_extraction let op_Star_Percent_Hat a b = mul_mod a b

inline_for_extraction val op_Amp_Hat: t -> t -> Tot t
inline_for_extraction let op_Amp_Hat a b = logand a b
inline_for_extraction val op_Hat_Hat: t -> t -> Tot t
inline_for_extraction let op_Hat_Hat a b = logxor a b
inline_for_extraction val op_Bar_Hat: t -> t -> Tot t
inline_for_extraction let op_Bar_Hat a b = logor a b

(* Shift operators *)
inline_for_extraction val op_Greater_Greater_Hat: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction let op_Greater_Greater_Hat a s = shift_right a s

inline_for_extraction val op_Less_Less_Hat: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})
inline_for_extraction let op_Less_Less_Hat a s = shift_left a s

(* To input / output constants *)
assume val of_string: string -> Tot t
