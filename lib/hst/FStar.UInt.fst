module FStar.UInt
open FStar.Mul
open Math.Lemmas

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fst], which is mostly
 * a copy-paste of this module. *)

(* Specs. Note: lacking any type of functors for F*, this is a copy/paste of [FStar.Int.fst], where
 * the relevant bits that changed are:
 * - definition of max and min
 * - use of regular integer modulus instead of wrap-around modulus *)
let max_int (n:nat) : Tot int = pow2 n - 1
let min_int (n:nat) : Tot int = 0

let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
type uint_t (n:nat) = x:int{size x n}

(* Constants *)
val zero: n:pos -> Tot (uint_t n)
let zero n = 0
val one: n:pos -> Tot (uint_t n)
let one n = 1
val ones: n:pos -> Tot (uint_t n)
let ones n = max_int n

(* Increment and decrement *)
val incr: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
let incr #n a =
  a + 1
val decr: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
let decr #n a =
  a - 1

abstract val incr_underspec: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))
let incr_underspec #n a =
  if a < max_int n then a + 1 else magic()

abstract val decr_underspec: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))
let decr_underspec #n a =
  if a > min_int n then a - 1 else magic()

val incr_mod: #n:pos -> a:uint_t n -> Tot (uint_t n)
let incr_mod #n a = (a + 1) % (pow2 n)
val decr_mod: #n:pos -> a:uint_t n -> Tot (uint_t n)
let decr_mod #n a = (a - 1) % (pow2 n)

(* Addition primitives *)
val add: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
let add #n a b =
  a + b

abstract val add_underspec: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))
let add_underspec #n a b =
  if fits (a+b) n then a + b else magic ()

val add_mod: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
let add_mod #n a b =
  (a + b) % (pow2 n)

(* Subtraction primitives *)
val sub: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
let sub #n a b =
  a - b

abstract val sub_underspec: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))
let sub_underspec #n a b =
  if fits (a-b) n then a - b else magic ()

val sub_mod: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let sub_mod #n a b =
  (a - b) % (pow2 n)

(* Multiplication primitives *)
val mul: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
let mul #n a b =
  a * b

abstract val mul_underspec: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))
let mul_underspec #n a b =
  if fits (a*b) n then a * b else magic ()

val mul_mod: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let mul_mod #n a b =
  (a * b) % (pow2 n)

(* Division primitives *)
val div: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
let div #n a b =
  a / b

abstract val div_underspec: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))
let div_underspec #n a b =
  if fits (a / b) n then a / b else magic ()

(* Modulo primitives *)
// JK: takes time
val mod: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Tot (uint_t n)
let mod #n a b = a - ((a/b) * b)

(* Bitwise operators *)
assume val logand: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
assume val logxor: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
assume val logor: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
assume val lognot: #n:pos -> uint_t n -> Tot (uint_t n)

(* Comparison operators *)
let eq #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
let gt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
let lt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

(* JK: bitwise logic should be expressed usint a separate bitvector type   *)

(** This is not a complete bitvector type, there exist only several basic    **)
(** functions which are used to prove the assumed lemmas.                    **)
(** (nth' a i) returns a 1-bit integer indicating the i-th bit of a.        **)
(** (nth a i) returns a boolean indicating the i-th bit of a.                **)
(** (rest a i) returns a (n-1)-bit integer made of the last (n-1) bits of a. **)
(** A complete bitvector type should contain more functions like "sub",      **)
(** whose proof will be similar with the one of "rest" but more complicated. **)
private let nth' #n (a:uint_t n) (i:int) : Tot (uint_t 1) = 
  if i < 0 then 0 else (a / pow2 i) % pow2 1
private let rest (#n:pos) (a:uint_t n) : Tot (uint_t (n - 1)) = a % pow2 (n - 1)

let nth #n (a:uint_t n) (i:nat{i < n}) : Tot bool = (nth' #n a i = 1)

private val rest_lemma_aux: #n:pos -> a:uint_t n -> i:nat{i < n - 1} ->
  Lemma (requires True)
        (ensures (nth' (rest a) i = nth' a i))
        [SMTPat (nth (rest a) i)]
let rest_lemma_aux #n a i = 
  modulo_division_lemma a (pow2 i) (pow2 (n - i - 1));
  pow2_exp_1 i (n - i - 1);
  nat_over_pos_is_nat a (pow2 i);
  modulo_modulo_lemma (a / pow2 i) (pow2 1) (pow2 (n - i - 2));
  pow2_exp_1 1 (n - i - 2)

private val rest_lemma: #n:pos -> a:uint_t n ->
  Lemma (forall i. nth (rest a) i = nth a i)
let rest_lemma #n a = ()

private val rest_value_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires (nth a (n - 1)))
	(ensures (a = pow2 (n - 1) + rest a))
let rest_value_lemma_1 #n a = 
  nat_over_pos_is_nat a (pow2 (n - 1));
  small_modulo_lemma_1 (a / pow2 (n - 1)) (pow2 1);
  euclidian_division_definition a (pow2 (n - 1))

private val rest_value_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires (not (nth a (n - 1))))
	(ensures (a = rest a))
let rest_value_lemma_2 #n a = 
  nat_over_pos_is_nat a (pow2 (n - 1));
  small_modulo_lemma_1 (a / pow2 (n - 1)) (pow2 1);
  euclidian_division_definition a (pow2 (n - 1))

val nth_lemma: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires forall i. nth a i = nth b i) (ensures a = b)
let rec nth_lemma #n a b = 
  if n = 0 then () else begin
    if nth a (n - 1) then begin
      rest_value_lemma_1 #n a; rest_value_lemma_1 #n b;
      rest_lemma #n a; rest_lemma #n b;
      nth_lemma #(n - 1) (rest #n a) (rest #n b)
    end else begin
      rest_value_lemma_2 #n a; rest_value_lemma_2 #n b;
      rest_lemma #n a; rest_lemma #n b;
      nth_lemma #(n - 1) (rest #n a) (rest #n b)
    end
  end

(* Lemmas for constants *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (zero n) i = false))
        [SMTPat (nth (zero n) i)]
let zero_nth_lemma #n i = ()

val one_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = 0 ==> nth (one n) i = true) /\
	         (i > 0 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]
let one_nth_lemma #n i = ()

val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]
let ones_nth_lemma #n i =
  pow2_exp_1 i (n - i);
  division_definition (pow2 n - 1) (pow2 i) (pow2 (n - i) - 1)

(* Bitwise operators definitions *)
assume val logand_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logand a b) i = (nth a i && nth b i)))
	[SMTPat (nth (logand a b) i)]
assume val logxor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logxor a b) i = (nth a i <> nth b i)))
	[SMTPat (nth (logxor a b) i)]
assume val logor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logor a b) i = (nth a i || nth b i)))
	[SMTPat (nth (logor a b) i)]
assume val lognot_definition: #n:pos -> a:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (lognot a) i = not(nth a i)))
	[SMTPat (nth (lognot a) i)]

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
val logand_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))
let logand_commutative #n a b = nth_lemma #n (logand #n a b) (logand #n b a)

val logand_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
	(ensures (logand #n (logand #n a b) c = logand #n a (logand #n b c)))
let logand_associative #n a b c = nth_lemma #n (logand #n (logand #n a b) c) (logand #n a (logand #n b c))

val logand_self: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logand #n a a = a))
let logand_self #n a = nth_lemma #n (logand #n a a) a

val logand_lemma_1: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))
let logand_lemma_1 #n a = nth_lemma #n (logand #n a (zero n)) (zero n)

val logand_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logand #n a (ones n) = a))
let logand_lemma_2 #n a = nth_lemma #n (logand #n a (ones n)) a

(* Bitwise XOR operator *)
val logxor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))
let logxor_commutative #n a b = nth_lemma #n (logxor #n a b) (logxor #n b a)

val logxor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))
let logxor_associative #n a b c = nth_lemma #n (logxor #n (logxor #n a b) c) (logxor #n a (logxor #n b c))

val logxor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))
let logxor_self #n a = nth_lemma #n (logxor #n a a) (zero n)

val logxor_lemma_1: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))
let logxor_lemma_1 #n a = nth_lemma #n (logxor #n a (zero n)) a

val logxor_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))
let logxor_lemma_2 #n a = nth_lemma #n (logxor #n a (ones n)) (lognot #n a)

(* Bitwise OR operators *)
val logor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logor #n a b = logor #n b a))
let logor_commutative #n a b = nth_lemma #n (logor #n a b) (logor #n b a)

val logor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
	(ensures (logor #n (logor #n a b) c = logor #n a (logor #n b c)))
let logor_associative #n a b c = nth_lemma #n (logor #n (logor #n a b) c) (logor #n a (logor #n b c))

val logor_self: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logor #n a a = a))
let logor_self #n a = nth_lemma #n (logor #n a a) a

val logor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (zero n) = a))
let logor_lemma_1 #n a = nth_lemma (logor #n a (zero n)) a

val logor_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logor #n a (ones n) = ones n))
let logor_lemma_2 #n a = nth_lemma (logor #n a (ones n)) (ones n)

(* Bitwise NOT operator *)
val lognot_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (lognot #n (lognot #n a) = a))
let lognot_self #n a = nth_lemma (lognot #n (lognot #n a)) a

val lognot_lemma_1: #n:pos -> 
  Lemma (requires True) (ensures (lognot #n (zero n) = ones n))
let lognot_lemma_1 #n = nth_lemma (lognot #n (zero n)) (ones n)

(* Casts *)
val to_uint_t: m:pos -> a:int -> Tot (uint_t m)
let to_uint_t m a = a % pow2 m

(* Shift operators *)
val shift_right: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_right #n a s = 
  slash_decr_axiom a (pow2 s);
  nat_over_pos_is_nat a (pow2 s);
  a / (pow2 s)

val shift_left: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_left #n a s = (a * (pow2 s)) % pow2 n

private val shift_right_lemma_aux: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n} ->
  Lemma (nth' (shift_right #n a s) i = (a / pow2 (s + i)) % pow2 1)
let shift_right_lemma_aux #n a s i =
  division_multiplication_lemma a (pow2 s) (pow2 i);
  pow2_exp_1 s i

val shift_right_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
	(ensures (nth (shift_right #n a s) i = false))
	[SMTPat (nth (shift_right #n a s) i)]
let shift_right_lemma_1 #n a s i =
  shift_right_lemma_aux #n a s i;
  pow2_increases_2 (s + i) n;
  small_division_lemma_1 a (pow2 (s + i))

val shift_right_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i + s)))
	[SMTPat (nth (shift_right #n a s) i)]
let shift_right_lemma_2 #n a s i =
  shift_right_lemma_aux #n a s i

private val shift_left_lemma_aux_0: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n} ->
  Lemma (nth' (shift_left #n a s) i = ((a * pow2 s) / pow2 i) % pow2 1)
let shift_left_lemma_aux_0 #n a s i =
  modulo_division_lemma (a * pow2 s) (pow2 i) (pow2 (n - i));
  pow2_exp_1 i (n - i);
  nat_over_pos_is_nat (a * pow2 s) (pow2 i);
  modulo_modulo_lemma ((a * pow2 s) / pow2 i) (pow2 1) (pow2 (n - i - 1));
  pow2_exp_1 1 (n - i - 1)

private val shift_left_lemma_aux_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (((a * pow2 s) / pow2 i) % pow2 1 = 0)
let shift_left_lemma_aux_1 #n a s i = 
  pow2_exp_1 (s - i) i;
  commutativity_mul a (pow2 (s - i)) (pow2 i);
  multiple_division_lemma (a * pow2 (s - i)) (pow2 i);
  assert(((a * pow2 s) / pow2 i) % pow2 1 = (a * pow2 (s - i)) % pow2 1);
  pow2_exp_1 (s - i - 1) 1;
  commutativity_mul a (pow2 (s - i - 1)) (pow2 1);
  multiple_modulo_lemma (a * pow2 (s - i - 1)) (pow2 1);
  assert(((a * pow2 s) / pow2 i) % pow2 1 = 0)
  
private val shift_left_lemma_aux_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma ((a * pow2 s) / pow2 i = a / pow2 (i - s))
let shift_left_lemma_aux_2 #n a s i =
  pow2_exp_1 s (i - s);
  division_multiplication_lemma (a * pow2 s) (pow2 s) (pow2 (i - s));
  multiple_division_lemma a (pow2 s)
	
val shift_left_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
	(ensures (nth (shift_left #n a s) i = false))
	[SMTPat (nth (shift_left #n a s) i)]
let shift_left_lemma_1 #n a s i =
  shift_left_lemma_aux_0 #n a s i;
  shift_left_lemma_aux_1 #n a s i

val shift_left_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_left #n a s) i)]
let shift_left_lemma_2 #n a s i =
  shift_left_lemma_aux_0 #n a s i;
  shift_left_lemma_aux_2 #n a s i

val shift_right_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logxor #n a b) s = logxor #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logxor_lemma #n a b s = nth_lemma (shift_right #n (logxor #n a b) s) (logxor #n (shift_right #n a s) (shift_right #n b s))

val shift_left_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logxor #n a b) s = logxor #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logxor_lemma #n a b s = nth_lemma (shift_left #n (logxor #n a b) s) (logxor #n (shift_left #n a s) (shift_left #n b s))


(* val lemma_pow2_values: n:nat -> Lemma *)
(*   (requires (n <= 64)) *)
(*   (ensures  (pow2 0 = 1 *)
(*     /\ pow2 1 = 2 *)
(*     /\ pow2 2 = 4 *)
(*     /\ pow2 3 = 8 *)
(*     /\ pow2 4 = 16 *)
(*     /\ pow2 5 = 32 *)
(*     /\ pow2 6 = 64 *)
(*     /\ pow2 7 = 128 *)
(*     /\ pow2 8 = 256 *)
(*     /\ pow2 9 = 512 *)
(*     /\ pow2 10 = 1024 *)
(*     /\ pow2 11 = 2048 *)
(*     /\ pow2 12 = 4096 *)
(*     /\ pow2 13 = 8192 *)
(*     /\ pow2 14 = 16384 *)
(*     /\ pow2 15 = 32768 *)
(*     /\ pow2 16 = 65536 *)
(*     /\ pow2 17 = 131072 *)
(*     /\ pow2 18 = 262144 *)
(*     /\ pow2 19 = 524288 *)
(*     /\ pow2 20 = 1048576 *)
(*     /\ pow2 21 = 2097152 *)
(*     /\ pow2 22 = 4194304 *)
(*     /\ pow2 23 = 8388608 *)
(*     /\ pow2 24 = 16777216 *)
(*     /\ pow2 25 = 33554432 *)
(*     /\ pow2 26 = 67108864 *)
(*     /\ pow2 27 = 134217728 *)
(*     /\ pow2 28 = 268435456 *)
(*     /\ pow2 29 = 536870912 *)
(*     /\ pow2 30 = 1073741824 *)
(*     /\ pow2 31 = 2147483648 *)
(*     /\ pow2 32 = 4294967296 *)
(*     /\ pow2 33 = 8589934592 *)
(*     /\ pow2 34 = 17179869184 *)
(*     /\ pow2 35 = 34359738368 *)
(*     /\ pow2 36 = 68719476736 *)
(*     /\ pow2 37 = 137438953472 *)
(*     /\ pow2 38 = 274877906944 *)
(*     /\ pow2 39 = 549755813888 *)
(*     /\ pow2 40 = 1099511627776 *)
(*     /\ pow2 41 = 2199023255552 *)
(*     /\ pow2 42 = 4398046511104 *)
(*     /\ pow2 43 = 8796093022208 *)
(*     /\ pow2 44 = 17592186044416 *)
(*     /\ pow2 45 = 35184372088832 *)
(*     /\ pow2 46 = 70368744177664 *)
(*     /\ pow2 47 = 140737488355328 *)
(*     /\ pow2 48 = 281474976710656 *)
(*     /\ pow2 49 = 562949953421312 *)
(*     /\ pow2 50 = 1125899906842624 *)
(*     /\ pow2 51 = 2251799813685248 *)
(*     /\ pow2 52 = 4503599627370496 *)
(*     /\ pow2 53 = 9007199254740992 *)
(*     /\ pow2 54 = 18014398509481984 *)
(*     /\ pow2 55 = 36028797018963968 *)
(*     /\ pow2 56 = 72057594037927936 *)
(*     /\ pow2 57 = 144115188075855872 *)
(*     /\ pow2 58 = 288230376151711744 *)
(*     /\ pow2 59 = 576460752303423488 *)
(*     /\ pow2 60 = 1152921504606846976 *)
(*     /\ pow2 61 = 2305843009213693952 *)
(*     /\ pow2 62 = 4611686018427387904 *)
(*     /\ pow2 63 = 9223372036854775808 *)
(*     /\ pow2 64 = 18446744073709551616 )) *)
(*     [SMTPat (pow2 n)] *)
(* let lemma_pow2_values n = admit() *)

(* assume Lemma_pow2_values: *)
(*   (pow2 0 = 1 /\ pow2 1 = 2 /\ pow2 2 = 4 /\ pow2 3 = 8 *)
(*     /\ pow2 4 = 16 /\ pow2 5 = 32 /\ pow2 6 = 64 /\ pow2 7 = 128 *)
(*     /\ pow2 8 = 256 /\ pow2 9 = 512 /\ pow2 10 = 1024 /\ pow2 11 = 2048 *)
(*     /\ pow2 12 = 4096 /\ pow2 13 = 8192 /\ pow2 14 = 16384 /\ pow2 15 = 32768 *)
(*     /\ pow2 16 = 65536 /\ pow2 17 = 131072 /\ pow2 18 = 262144 /\ pow2 19 = 524288 *)
(*     /\ pow2 20 = 1048576 /\ pow2 21 = 2097152 /\ pow2 22 = 4194304 /\ pow2 23 = 8388608 *)
(*     /\ pow2 24 = 16777216 /\ pow2 25 = 33554432 /\ pow2 26 = 67108864 /\ pow2 27 = 134217728 *)
(*     /\ pow2 28 = 268435456 /\ pow2 29 = 536870912 /\ pow2 30 = 1073741824 /\ pow2 31 = 2147483648 *)
(*     /\ pow2 32 = 4294967296 /\ pow2 33 = 8589934592 /\ pow2 34 = 17179869184 /\ pow2 35 = 34359738368 *)
(*     /\ pow2 36 = 68719476736 /\ pow2 37 = 137438953472 /\ pow2 38 = 274877906944 /\ pow2 39 = 549755813888 *)
(*     /\ pow2 40 = 1099511627776 /\ pow2 41 = 2199023255552 /\ pow2 42 = 4398046511104 /\ pow2 43 = 8796093022208 *)
(*     /\ pow2 44 = 17592186044416 /\ pow2 45 = 35184372088832 /\ pow2 46 = 70368744177664 /\ pow2 47 = 140737488355328 *)
(*     /\ pow2 48 = 281474976710656 /\ pow2 49 = 562949953421312 /\ pow2 50 = 1125899906842624 /\ pow2 51 = 2251799813685248 *)
(*     /\ pow2 52 = 4503599627370496 /\ pow2 53 = 9007199254740992 /\ pow2 54 = 18014398509481984 /\ pow2 55 = 36028797018963968 *)
(*     /\ pow2 56 = 72057594037927936 /\ pow2 57 = 144115188075855872 /\ pow2 58 = 288230376151711744 /\ pow2 59 = 576460752303423488 *)
(*     /\ pow2 60 = 1152921504606846976 /\ pow2 61 = 2305843009213693952 /\ pow2 62 = 4611686018427387904 /\ pow2 63 = 9223372036854775808 *)
(*     /\ pow2 64 = 18446744073709551616) *)
