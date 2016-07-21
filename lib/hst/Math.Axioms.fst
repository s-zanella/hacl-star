module Math.Axioms

open FStar.Mul

(** Necessary axioms **)
(* Axiom: Definition of modulo operator *)
assume val neg_modulo: a:int -> b:pos -> Lemma ((-a) % b = (b - (a % b)) % b)


(* Lemma: Definition of euclidian division *)
val euclidian_division_definition:  a:nat -> b:pos ->
    Lemma (a = (a / b) * b + (a % b))
let euclidian_division_definition a b = ()

(* Lemma: Multiplication by a positive integer preserves order *)
val multiplication_order_lemma: a:nat -> b:nat -> p:pos ->
    Lemma (a > b <==> a * p > b * p)
let multiplication_order_lemma a b p = ()

(* Lemma: Propriety about multiplication after division *)
val division_propriety: a:nat -> b:pos ->
    Lemma (a - b < (a / b) * b && (a / b) * b <= a)
let division_propriety a b = ()

(* Internal lemmas for proving the definition of division *)
private val division_definition_lemma_1: a:nat -> b:pos -> m:nat{a - b < m * b} ->
    Lemma (m > (a / b) - 1)
let division_definition_lemma_1 a b m = 
  if (a / b) - 1 < 0 then () else begin
    division_propriety a b;
    multiplication_order_lemma m ((a / b) - 1) b
  end
private val division_definition_lemma_2: a:nat -> b:pos -> m:nat{m * b <= a} ->
    Lemma (m < (a / b) + 1)
let division_definition_lemma_2 a b m =
  division_propriety a b;
  multiplication_order_lemma ((a / b) + 1) m b

(* Lemma: Definition of division *)
val division_definition: a:nat -> b:pos -> m:nat{a - b < m * b && m * b <= a} ->
    Lemma (m = a / b)
let division_definition a b m =
  division_definition_lemma_1 a b m;
  division_definition_lemma_2 a b m
  
(* Lemma: a * b / b = a *)
val multiple_division_lemma: a:nat -> b:pos -> Lemma ( (a * b) / b = a )
let multiple_division_lemma a b = division_definition (a * b) b a

(* Lemma: a * b % b = 0 *)
val multiple_modulo_lemma: a:nat -> b:pos -> Lemma ( (a * b) % b = 0 )
let multiple_modulo_lemma a b = 
  euclidian_division_definition (a * b) b;
  multiple_division_lemma a b

(* Lemma: Division distributivity under special condition *)
val division_addition_lemma: a:nat -> b:pos -> n:nat ->
    Lemma ( (a + n * b) / b = (a / b) + n )
let division_addition_lemma a b n = division_definition (a + n * b) b ((a / b) + n)

(* Lemma: Modulo distributivity *)
val modulo_addition_lemma: a:nat -> b:nat -> c:pos ->
    Lemma ( (a + b) % c = (a % c + b % c) % c )
let modulo_addition_lemma a b c =
  euclidian_division_definition a c;
  euclidian_division_definition b c;
  division_addition_lemma (a - (a / c) * c + b - (b / c) * c) c (a / c + b / c)

(** Old Necessary axioms **)
(* Old Axiom: euclidian division on nats yield a smaller output than its input *)
val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a)
let slash_decr_axiom a b =
  euclidian_division_definition a b;
  if a / b = 0 then () else multiplication_order_lemma b 1 (a / b)
  
(* Old Axiom: definition of the "b divides c" relation *)
val slash_star_axiom: a:int -> b:pos -> c:nat ->
    Lemma (requires (a * b = c)) (ensures (a = c / b))
let slash_star_axiom a b c =
  if a >= 0 then multiple_division_lemma a b
  else multiple_division_lemma (-a) b
  
(* Old Axiom: the opposite of a multiple of b is also a multiple of b and vice-versa *)
val neg_of_multiple_is_multiple: a:int -> b:pos -> Lemma 
  (requires (a % b = 0)) 
  (ensures ((-a) % b = 0))
let neg_of_multiple_is_multiple a b = neg_modulo a b
val neg_of_non_multiple_is_non_multiple: a:int -> b:pos -> Lemma
    (requires (a % b <> 0))
    (ensures ((-a) % b <> 0))
let neg_of_non_multiple_is_non_multiple a b = neg_modulo a b


(** Usefull lemmas for future proofs **)
val modulo_lemma_0: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let modulo_lemma_0 a b = ()

(* Lemma: definition of the euclidian division for nats *)
val euclidian_div_axiom:
  a:nat -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( a - b * (a / b) >= 0 /\ a - b * (a / b) < b ))
let euclidian_div_axiom a b = ()

(* Lemma: multiplication is right distributive over addition *)
val distributivity_add_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( (a + b) * c = a * c + b * c ))
let distributivity_add_left a b c = ()

(* Lemma: multiplication is left distributive over addition *)
val distributivity_add_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b + c) = a * b + a * c ))
let distributivity_add_right a b c = ()

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b - c) = a * b - a * c ))
let distributivity_sub_right a b c = ()

(* Lemma: multiplication is commutative, hence parenthesizing is meaningless *)
val paren_mul_left:
  a:int -> b:int -> c:int ->
  Lemma 
    (requires (True))
    (ensures ( a * b * c = ( a * b ) * c))
let paren_mul_left a b c = ()

(* Lemma: multiplication is commutative, hence parenthesizing is meaningless *)
val paren_mul_right:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures ( a * b * c = a * (b * c) ))
let paren_mul_right a b c = ()

(* Lemma: addition is commutative, hence parenthesizing is meaningless *)
val paren_add_left:
  a:int -> b:int -> c:int ->
  Lemma 
    (requires (True))
    (ensures ( a + b + c = ( a + b ) + c))
let paren_add_left a b c = ()

(* Lemma: addition is commutative, hence parenthesizing is meaningless *)
val paren_add_right:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures ( a + b + c = a + (b + c) ))
let paren_add_right a b c = ()

val addition_is_associative: a:int -> b:int -> c:int -> 
  Lemma (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))
let addition_is_associative a b c = ()

val subtraction_is_distributive: a:int -> b:int -> c:int -> 
  Lemma (a - b + c = (a - b) + c /\ a - b - c = a - (b + c) /\ a - b - c = (a - b) - c
	/\ a + (-b-c) = a - b - c)
let subtraction_is_distributive a b c = ()

val swap_add_plus_minus:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
    (ensures ( a + b - c = (a - c) + b ))
let swap_add_plus_minus a b c = ()

(* Lemma: multiplication on integers is commutative *)
val swap_mul:
  a:int -> b:int ->
  Lemma (requires (True))
 (ensures ( a * b = b * a ))
let swap_mul a b = ()

(* Lemma: minus applies to the whole term *)
val neg_mul_left:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = (-a) * b ))
let neg_mul_left a b = ()

(* Lemma: minus applies to the whole term *)
val neg_mul_right:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = a * (-b)))
let neg_mul_right a b = ()

val swap_neg_mul:
   a:int -> b:int ->
   Lemma
     (requires (True))
     (ensures ( (-a) * b = a * (-b)))
let swap_neg_mul a b =
  neg_mul_left a b;
  neg_mul_right a b
  
(* Lemma: multiplication precedence on addition *)
val mul_binds_tighter:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures (
  a + (b * c) = a + b * c
       ))
let mul_binds_tighter a b c = ()

(* Lemma: multiplication keeps symetric bounds :
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
val mul_ineq1:
  a:int -> b:nat -> c:int -> d:nat ->
  Lemma
    (requires ( a < b /\ a > -b /\ c < d /\ c > -d))
    (ensures (a * c < b * d /\ a * c > - (b * d)))
let mul_ineq1 a b c d = ()

val nat_times_nat_is_nat:
  a:nat -> b:nat -> 
  Lemma (requires (True))
	(ensures (a * b >= 0))
let nat_times_nat_is_nat a b = ()

val pos_times_pos_is_pos:
  a:pos -> b:pos -> 
  Lemma (requires (True))
	(ensures (a * b > 0))
let pos_times_pos_is_pos a b = ()

val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)
let nat_over_pos_is_nat a b = ()
