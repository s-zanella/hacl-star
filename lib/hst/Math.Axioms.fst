module Math.Axioms

open FStar.Mul

(** The definition of div and mod in Z3 follows that in SMT-LIB,  **)
(** which is                                                      **)
(**     0 <= a mod b < b  &&  a = (a div b) * b + (a mod b),      **)
(** this means div and mod are defined in pairs.                  **)
(** However, div in F* requires that the dividend is natural      **)
(** while mod does not have this restriction. Therefore, an       **)
(** additional definition of mod for negative numbers is needed.  **)
(** Personally I do not think this one can be proved before       **)
(** removing the restriction of div.    -- Jianyang               **)

(* Axiom: Definition of modulo operator *)
assume val neg_modulo: a:int -> b:pos -> Lemma ((-a) % b = (b - (a % b)) % b)
