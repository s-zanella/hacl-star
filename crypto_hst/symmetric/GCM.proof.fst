module GCM.Proof

open FStar.UInt
open Math.Lemmas

(* * A type for the group Z_2 **)
(* * Formally we also need to prove the addition and multiplication of Z_2 **)
(* * come from those of Z, the integer group, in the sense of modulo 2.    **)
type z2 = bool
let z2_0:z2 = false
let z2_1:z2 = true
let z2_add (a:z2) (b:z2) : Tot z2 = (a <> b)
let z2_mul (a:z2) (b:z2) : Tot z2 = (a && b)

(* Sum_{s <= i < t} a_i *)
val z2_sigma: s:int -> t:int{s <= t} -> a:(i:int{i >= s && i < t} -> Tot z2) ->
  Tot z2 (decreases (t - s))
let rec z2_sigma s t a =
  if s >= t then z2_0 else z2_add (a s) (z2_sigma (s + 1) t a)

(* * (z2x n): a polynomial over Z_2 with degree less than n. (ring Z_2[x])   **)
(* * Now it's based on FStar.UInt, but BitVector should be a better choice.  **)
type z2x (n:pos) = uint_t n

val coef: #n:pos -> p:(z2x n) -> i:nat{i < n} -> Tot bool
let coef #n p i = nth #n p i

val coef_lemma: #n:pos -> p1:(z2x n) -> p2:(z2x n) ->
  Lemma (requires (forall i. coef p1 i = coef p2 i))
	(ensures (p1 = p2))
let coef_lemma #n p1 p2 = nth_lemma #n p1 p2

val expand: #m:pos -> #n:nat{m <= n} -> p:(z2x m) -> Tot (p':z2x n{p = p'})
let expand #m #n p =
  pow2_increases_2 n m;
  let p':int = p in
  p'

(* Addition of Z_2[x], p1(x) + p2(x) *)
val add: #n:pos -> #m:pos{m <= n} -> p1:(z2x n) -> p2:(z2x m) -> Tot (z2x n)
let add #n #m p1 p2 = logxor #n p1 (expand #m #n p2)

(* The addition follows the definition *)
val add_lemma: #n:pos -> #m:pos{m <= n} -> p1:(z2x n) -> p2:(z2x m) ->
  Lemma (requires True)
	(ensures (forall i. coef (add p1 (expand #m #n p2)) i = z2_add (coef p1 i) (coef (expand #m #n p2) i)))
let add_lemma #n #m p1 p2 = ()

(* Multiplication of Z_2[x], p1(x)p2(x) *)
val mul: #n:pos -> #m:pos -> p1:(z2x n) -> p2:(z2x m) -> Tot (z2x (n + m - 1))
let mul #n #m p1 p2 = admit()

(* Let p(x)_k be the coefficient of term x^k in p(x).          *)
(* (mul_aux #n #m #i p1 p2 j) gives   p1(x)_j * p2(x)_{i-j}    *)
(* if j and (i-j) are all in the range. It gives 0 otherwise.  *)
val mul_aux: #n:pos -> #m:pos -> #i:nat{i < n + m - 1} -> p1:(z2x n) -> p2:(z2x m) -> j:int{j >= 0 && j <= i} -> Tot z2
let mul_aux #n #m #i p1 p2 j =
  if j >= n || i - j >= m then z2_0
  else z2_mul (coef p1 j) (coef p2 (i - j))

(* The multiplication follows the definition *)
val mul_lemma: #n:pos -> #m:pos -> p1:(z2x n) -> p2:(z2x m) ->
  Lemma (requires True)
	(ensures (forall i. coef #(n + m - 1) (mul #n #m p1 p2) i = z2_sigma 0 i (mul_aux #n #m #i p1 p2)))
let mul_lemma #n #m p1 p2 = admit()

(* Consider only non-trivial case *)
val div: #n:pos -> #m:pos{m <= n} -> p1:(z2x n) -> p2:(z2x m) -> Tot (z2x (n - m + 1))
let div #n #m p1 p2 = admit()

val mod: #n:pos -> #m:pos{m <= n} -> p1:(z2x n) -> p2:(z2x m) -> Tot (z2x m)
let mod #n #m p1 p2 = admit()

(* The division and modulo follows the definition *)
val divmod_lemma: #n:pos -> #m:pos{m <= n} -> p1:(z2x n) -> p2:(z2x m) ->
  Lemma (p1 = mul #(n - m + 1) #m (div p1 p2) p2 + mod p1 p2)
let divmod_lemma #n #m p1 p2 = admit()
