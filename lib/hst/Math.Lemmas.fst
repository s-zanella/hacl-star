module Math.Lemmas

open FStar.Mul
open Math.Axioms

(* Old Lemmas *)
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
val distributivity_sub_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( (a - b) * c = a * c - b * c ))
let distributivity_sub_left a b c = ()

(* Lemma: multiplication is right distributive over substraction *)
val distributivity_sub_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b - c) = a * b - a * c ))
let distributivity_sub_right a b c = ()

(* Lemma: multiplication is commutative *)
val commutativity_mul:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
  (ensures ( (a * b) * c = a * (b * c) ))
let commutativity_mul a b c = ()

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

(* Lemma: the opposite of a multiple of b is also a multiple of b and vice-versa *)
val neg_of_multiple_is_multiple: a:int -> b:pos -> Lemma 
  (requires (a % b = 0)) 
  (ensures ((-a) % b = 0))
let neg_of_multiple_is_multiple a b = neg_modulo a b
val neg_of_non_multiple_is_non_multiple: a:int -> b:pos -> Lemma
    (requires (a % b <> 0))
    (ensures ((-a) % b <> 0))
let neg_of_non_multiple_is_non_multiple a b = neg_modulo a b
    
val nat_mul_1: a:nat -> b:nat -> Lemma (requires True) (ensures (a*b >= 0))
let nat_mul_1 a b = ()

(* Lemma : multiplying by a strictly positive value preserves strict inequalities *)
val mul_pos_strict_incr: a:pos -> b:int -> c:pos -> Lemma (requires (b < c)) (ensures (a * b < a * c /\ b * a < c * a ))
let mul_pos_strict_incr a b c = ()

(* Lemma : multiplying by a positive value preserves inequalities *)
val mul_incr : a:nat -> b:nat -> c:nat -> 
		     Lemma 
		       (requires ( b <= c))
		       (ensures ( a * b <= a * c /\ b * a <= c * a))
let mul_incr a b c = ()

(* Lemma : loss of precision in euclidian division *)
val multiply_fractions:
  a:nat -> n:pos ->
  Lemma
    (requires (True))
    (ensures ( n * ( a / n ) <= a ))
let multiply_fractions a n =
  (euclidian_div_axiom a n)

(* Lemma : distributivity of minus over parenthesized sum *)
val paren_sub: a:int -> b:int -> c:int -> Lemma ((a - (b + c) = a - b - c /\ a - (b - c) = a - b + c))
let paren_sub a b c = ()

val non_zero_nat_is_pos: i:nat -> Lemma (requires (i <> 0)) (ensures (i >= 1))
let non_zero_nat_is_pos i = ()

val non_zero_nat_is_pos_2: n:nat -> Lemma (requires (n<>0)) (ensures (n-1>=0))
let non_zero_nat_is_pos_2 n = ()

val nat_plus_nat_is_nat: n:nat -> m:nat -> Lemma (n+m>=0)
let nat_plus_nat_is_nat n m = ()

(** Lemmas about multiplication, division and modulo. **)
(** This part focuses on the situation where          **)
(** dividend: nat    divisor: pos                     **)
(** TODO: add triggers for certain lemmas.            **)

(* Lemma: Definition of euclidian division *)
val euclidian_division_definition: a:nat -> b:pos ->
    Lemma (a = (a / b) * b + a % b)
let euclidian_division_definition a b = ()

(* Lemma: Propriety about modulo *)
val modulo_range_lemma: a:int -> b:pos ->
    Lemma (a % b >= 0 && a % b < b)
let modulo_range_lemma a b = ()

val small_modulo_lemma_1: a:nat -> b:pos ->
    Lemma (requires a < b) (ensures a % b = a)
let small_modulo_lemma_1 a b = ()
val small_modulo_lemma_2: a:nat -> b:pos ->
    Lemma (requires a % b = a) (ensures a < b)
let small_modulo_lemma_2 a b = ()

val small_division_lemma_1: a:nat -> b:pos ->
    Lemma (requires a < b) (ensures a / b = 0)
let small_division_lemma_1 a b = ()
val small_division_lemma_2: a:nat -> b:pos ->
    Lemma (requires a / b = 0) (ensures a < b)
let small_division_lemma_2 a b = ()

(* Lemma: Multiplication by a positive integer preserves order *)
val multiplication_order_lemma: a:nat -> b:nat -> p:pos ->
    Lemma (a >= b <==> a * p >= b * p)
let multiplication_order_lemma a b p = ()

(* Lemma: Propriety about multiplication after division *)
val division_propriety: a:nat -> b:pos ->
    Lemma (a - b < (a / b) * b && (a / b) * b <= a)
let division_propriety a b = ()

(* Internal lemmas for proving the definition of division *)
private val division_definition_lemma_1: a:nat -> b:pos -> m:nat{a - b < m * b} ->
    Lemma (m > a / b - 1)
let division_definition_lemma_1 a b m = 
  if a / b - 1 < 0 then () else begin
    division_propriety a b;
    multiplication_order_lemma m (a / b - 1) b
  end
private val division_definition_lemma_2: a:nat -> b:pos -> m:nat{m * b <= a} ->
    Lemma (m < a / b + 1)
let division_definition_lemma_2 a b m =
  division_propriety a b;
  multiplication_order_lemma (a / b + 1) m b

(* Lemma: Definition of division *)
val division_definition: a:nat -> b:pos -> m:nat{a - b < m * b && m * b <= a} ->
    Lemma (m = a / b)
let division_definition a b m =
  division_definition_lemma_1 a b m;
  division_definition_lemma_2 a b m
  
(* Lemma: (a * b) / b = a *)
val multiple_division_lemma: a:nat -> b:pos -> Lemma ( (a * b) / b = a )
let multiple_division_lemma a b = division_definition (a * b) b a

(* Lemma: (a * b) % b = 0 *)
val multiple_modulo_lemma: a:nat -> b:pos -> Lemma ( (a * b) % b = 0 )
let multiple_modulo_lemma a b = multiple_division_lemma a b

(* Lemma: Division distributivity under special condition *)
val division_addition_lemma: a:nat -> b:pos -> n:nat ->
    Lemma ( (a + n * b) / b = a / b + n )
let division_addition_lemma a b n = division_definition (a + n * b) b (a / b + n)

(* Lemma: Modulo distributivity *)
val modulo_distributivity: a:nat -> b:nat -> c:pos ->
    Lemma ( (a + b) % c = (a % c + b % c) % c )
let modulo_distributivity a b c =
  euclidian_division_definition a c;
  euclidian_division_definition b c;
  euclidian_division_definition (a % c + b % c) c;
  nat_over_pos_is_nat a c;
  nat_over_pos_is_nat b c;
  division_addition_lemma (a - (a / c) * c + b - (b / c) * c) c (a / c + b / c)

(* Lemma: Modulo distributivity under special condition *)
val modulo_addition_lemma: a:nat -> b:pos -> n:nat ->
    Lemma ( (a + n * b) % b = a % b )
let modulo_addition_lemma a b n =
  modulo_distributivity a (n * b) b;
  multiple_modulo_lemma n b

(* Lemma: Divided by a product is equivalent to being divided one by one *)
val division_multiplication_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ( a / (b * c) = (a / b) / c )
let division_multiplication_lemma a b c =
  if a / b <= c - 1 then begin
    small_division_lemma_1 (a / b) c;
    small_division_lemma_1 a (b * c)
  end else begin
    division_propriety (a / b) c;
    multiplication_order_lemma (a / b) (((a / b) / c) * c) b;
    multiplication_order_lemma (((a / b) / c) * c) ((a / b) - c) b;
    cut( ((a / b) - c + 1) * b <= (((a / b) / c) * c) * b );
    cut( (((a / b) / c) * c) * b <= (a / b) * b );
    nat_over_pos_is_nat a b;
    nat_over_pos_is_nat (a / b) c;
    division_definition a (b * c) ((a / b) / c)
  end

(* Lemma: Propriety about modulo and division *)
val modulo_division_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ( (a % (b * c)) / b = (a / b) % c )
let modulo_division_lemma a b c =
  division_addition_lemma (a - (a / (b * c)) * (b * c)) b ((a / (b * c)) * c);
  distributivity_sub_left a (a / (b * c)) (b * c);
  commutativity_mul (a / (b * c)) c b;
  cut( (a - (a / (b * c)) * (b * c)) / b = a / b - ((a / (b * c)) * c));
  euclidian_division_definition a (b * c);
  division_multiplication_lemma a b c;
  euclidian_division_definition (a / b) c

val modulo_modulo_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ( (a % (b * c)) % b = a % b )
let modulo_modulo_lemma a b c =
  modulo_addition_lemma (a - (a / (b * c)) * (b * c)) b ((a / (b * c)) * c);
  assert( ((a - (a / (b * c)) * (b * c)) + ((a / (b * c)) * c) * b) % b = (a - (a / (b * c)) * (b * c)) % b );
  cut( a % b = (a - (a / (b * c)) * (b * c)) % b );
  euclidian_division_definition a (b * c)

(* Lemma: mutiplying by a positive number yield a greater output than input *)
val star_incr_axiom: a:nat -> b:pos -> Lemma (a * b >= a)
let star_incr_axiom a b = if a = 0 then () else multiplication_order_lemma b 1 a

(* Lemma: euclidian division on nats yield a smaller output than its input *)
val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a)
let slash_decr_axiom a b =
  euclidian_division_definition a b;
  if a / b = 0 then () else multiplication_order_lemma b 1 (a / b)
  
(* Lemma: definition of the "b divides c" relation *)
val slash_star_axiom: a:int -> b:pos -> c:nat ->
    Lemma (requires (a * b = c)) (ensures (a = c / b))
let slash_star_axiom a b c =
  if a >= 0 then multiple_division_lemma a b
  else multiple_division_lemma (-a) b

val pow2_double_sum:
  n:nat -> Lemma (requires (True)) (ensures (pow2 n + pow2 n = pow2 (n+1))) 
let pow2_double_sum n =
  assert(n = ((n+1)-1));
  assert(pow2 n + pow2 n = 2 * pow2 n)

val pow2_double_mult:
  n:nat -> Lemma (requires (True)) (ensures (2 * pow2 n = pow2 (n+1)))
let pow2_double_mult n =
  assert(2 * pow2 n = pow2 n + pow2 n)

val pow2_increases_1:
  n:nat -> m:nat ->
  Lemma
    (requires (m < n))
    (ensures (pow2 m < pow2 n))
    (decreases (n-m))
let rec pow2_increases_1 n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_increases_1 (n-1) m; pow2_increases_1 n (n-1)

val pow2_increases_2:
  n:nat -> m:nat ->
  Lemma
    (requires (m <= n))
    (ensures (pow2 m <= pow2 n))
    (decreases (n-m))
let pow2_increases_2 n m =
  match n-m with
  | 0 -> ()
  | _ -> pow2_increases_1 n m

val aux_lemma_0: n:nat -> m:nat -> Lemma ((n-1)+m+1 = n+m)
let aux_lemma_0 n m = ()

val aux_lemma_1: n:nat -> Lemma (0+n = n)
let aux_lemma_1 n = ()

val aux_lemma_2: n:nat -> Lemma (1 * n = n)
let aux_lemma_2 n = ()

val pow2_exp_1:
  n:nat -> m:nat -> 
  Lemma 
    (requires (True))
    (ensures (pow2 n * pow2 m = pow2 (n+m)))
    (decreases n)
let rec pow2_exp_1 n m =
  match n with
  | 0 -> 
    assert(b2t(pow2 n = 1));
    aux_lemma_1 m;
    aux_lemma_2 (pow2 m)
  | i -> 
    cut(i >= 0 /\ i <> 0); 
    cut(b2t(i >= 1)); 
    cut(b2t(n - 1 >= 0)); 
    pow2_exp_1 (n-1) (m); 
    cut(b2t(pow2 (n-1) * pow2 m = pow2 ((n-1)+m)));
    pow2_double_mult ((n-1)+m);
    cut(b2t(2 * pow2 ((n-1)+m) = pow2 ((n-1)+m+1)));
    aux_lemma_0 n m;
    cut(b2t( 2 * (pow2 (n-1) * pow2 m) = pow2 (n+m))); 
    paren_mul_left 2 (pow2 (n-1)) (pow2 m);
    paren_mul_right 2 (pow2 (n-1)) (pow2 m);
    pow2_double_mult (n-1)

val pow2_exp_2: n:nat -> m:nat{m <= n} ->
  Lemma (requires True)
        (ensures pow2 n / pow2 m = pow2 (n - m))
let pow2_exp_2 n m =
  pow2_exp_1 m (n - m);
  multiple_division_lemma (pow2 (n - m)) (pow2 m)
