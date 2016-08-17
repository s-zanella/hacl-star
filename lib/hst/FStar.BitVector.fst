module FStar.BitVector

open FStar.Mul
open FStar.Seq

(* Define bitwise operators with new type BitVector. *)
type bv_t (n:nat) = vec:seq bool{length vec = n}

(* Constants *)
val zero_vec: n:pos -> Tot (bv_t n)
let zero_vec n = create n false
val elem_vec: n:pos -> i:nat{i < n} -> Tot (bv_t n)
let elem_vec n i = upd (create n false) i true
val ones_vec: n:pos -> Tot (bv_t n)
let ones_vec n = create n true

(* Bitwise operators *)
val logand_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
let rec logand_vec #n a b = 
  if n = 1 then create 1 (index a 0 && index b 0)
  else append (create 1 (index a 0 && index b 0)) (logand_vec #(n - 1) (slice a 1 n) (slice b 1 n))
  
val logxor_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
let rec logxor_vec #n a b = 
  if n = 1 then create 1 (index a 0 <> index b 0)
  else append (create 1 (index a 0 <> index b 0)) (logxor_vec #(n - 1) (slice a 1 n) (slice b 1 n))
  
val logor_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
let rec logor_vec #n a b = 
  if n = 1 then create 1 (index a 0 || index b 0)
  else append (create 1 (index a 0 || index b 0)) (logor_vec #(n - 1) (slice a 1 n) (slice b 1 n))
  
val lognot_vec: #n:pos -> a:bv_t n -> Tot (bv_t n)
let rec lognot_vec #n a = 
  if n = 1 then create 1 (not (index a 0))
  else append (create 1 (not (index a 0))) (lognot_vec #(n - 1) (slice a 1 n))

(* Bitwise operators definitions *)
val logand_vec_definition: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (logand_vec #n a b) i = (index a i && index b i))
	[SMTPat (index (logand_vec #n a b) i)]
let rec logand_vec_definition #n a b i =
  if i = 0 then ()
  else logand_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

val logxor_vec_definition: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (logxor_vec #n a b) i = (index a i <> index b i))
	[SMTPat (index (logxor_vec #n a b) i)]
let rec logxor_vec_definition #n a b i =
  if i = 0 then ()
  else logxor_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

val logor_vec_definition: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (logor_vec #n a b) i = (index a i || index b i))
	[SMTPat (index (logor_vec #n a b) i)]
let rec logor_vec_definition #n a b i =
  if i = 0 then ()
  else logor_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

val lognot_vec_definition: #n:pos -> a:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (lognot_vec #n a) i = not (index a i))
	[SMTPat (index (lognot_vec #n a) i)]
let rec lognot_vec_definition #n a i =
  if i = 0 then ()
  else lognot_vec_definition #(n - 1) (slice a 1 n) (i - 1)


(* Define bitwise operators for type uint. *)
open FStar.UInt.BV
open Math.Lemmas

(* Casts *)
val to_vec: #n:nat -> num:uint_t n -> Tot (bv_t n)
let rec to_vec #n num =
  if n = 0 then createEmpty #bool
  else append (create 1 (num % 2 = 1)) (to_vec #(n - 1) (num / 2))

val from_vec: #n:nat -> vec:bv_t n -> Tot (uint_t n)
let rec from_vec #n vec =
  if n = 0 then 0
  else 2 * from_vec #(n - 1) (slice vec 1 n) + (if index vec 0 then 1 else 0)

val to_vec_bijection_lemma: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)
let rec to_vec_bijection_lemma #n a b =
  if n = 0 then () else begin
    assert(equal (slice (to_vec b) 1 n) (to_vec #(n - 1) (b / 2)));
    assert(equal (slice (to_vec a) 1 n) (to_vec #(n - 1) (a / 2)));
    to_vec_bijection_lemma #(n - 1) (a / 2) (b / 2);
    assert(a % 2 = (if index (to_vec a) 0 then 1 else 0));
    assert(b % 2 = (if index (to_vec b) 0 then 1 else 0));
    assert(a % 2 = b % 2)
  end

val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]
let rec inverse_aux #n vec i = 
  if i = 0 then () else inverse_aux #(n - 1) (slice vec 1 n) (i - 1)

val inverse_vec_lemma: #n:nat -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]
let inverse_vec_lemma #n vec = ()

val inverse_num_lemma: #n:nat -> num:uint_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]
let inverse_num_lemma #n num = to_vec_bijection_lemma #n num (from_vec (to_vec num))

val from_vec_bijection_lemma: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)
let from_vec_bijection_lemma #n a b = inverse_vec_lemma a; inverse_vec_lemma b


(* (nth a i) returns a boolean indicating the i-th bit of a. *)
val nth: #n:pos -> a:uint_t n -> i:nat{i < n} -> Tot bool
let nth #n a i = index (to_vec #n a) i

val nth_lemma: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)
let nth_lemma #n a b =
  assert(forall (i:nat{i < n}). index (to_vec #n a) i = index (to_vec #n b) i);
  to_vec_bijection_lemma a b

(* Lemmas for constants *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]
let rec zero_nth_lemma #n i =
  if i = 0 then () else zero_nth_lemma #(n - 1) (i - 1)

val one_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = 0 ==> nth (one n) i = true) /\
	         (i > 0 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]
let one_nth_lemma #n i =
  if i = 0 then () else zero_nth_lemma #(n - 1) (i - 1)

val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]
let rec ones_nth_lemma #n i =
  if i = 0 then () else begin
    pow2_exp_1 1 (n - 1);
    division_definition (pow2 n - 1) (pow2 1) (pow2 (n - 1) - 1);
    ones_nth_lemma #(n - 1) (i - 1)
  end

(* Bitwise operators *)
val logand: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logand #n a b = from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))
val logxor: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logxor #n a b = from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))
val logor: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logor #n a b = from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))
val lognot: #n:pos -> a:uint_t n  -> Tot (uint_t n)
let lognot #n a = from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
val logand_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logand a b) i = (nth a i && nth b i)))
	[SMTPat (nth (logand a b) i)]
let logand_definition #n a b i = ()
val logxor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logxor a b) i = (nth a i <> nth b i)))
	[SMTPat (nth (logxor a b) i)]
let logxor_definition #n a b i = ()
val logor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logor a b) i = (nth a i || nth b i)))
	[SMTPat (nth (logor a b) i)]
let logor_definition #n a b i = ()
val lognot_definition: #n:pos -> a:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (lognot a) i = not(nth a i)))
	[SMTPat (nth (lognot a) i)]
let lognot_definition #n a i = ()

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
