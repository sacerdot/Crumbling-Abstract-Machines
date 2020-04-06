(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "crumbles.ma".
include "variable finite set.ma".

notation "[ term 19 v ← term 19 b ]" non associative with precedence 90 for @{ 'substitution $v $b }.
interpretation "Substitution" 'substitution v b =(subst v b).

(*notation "〈 b break, e 〉" non associative with precedence 90 for @{ 'ccrumble $b $e }.
*)
interpretation "Crumble creation" 'pair b e =(CCrumble b e).

notation "𝛌 x . y" right associative with precedence 40 for @{ 'lambda $x $y}.
interpretation "Abstraction" 'lambda x y = (lambda x y ).

notation "ν x" non associative with precedence 90 for @{ 'variable $x}.
interpretation "Variable contruction" 'variable x = (variable x).

notation "hvbox(c @ e)" with precedence 35 for @{ 'at $c $e }.
interpretation "@ operation" 'at c e =(at c e).

definition var_from_subst ≝  λx:Substitution.
 match x with
 [ subst y z ⇒ y
 ]
.

let rec has_member l e on l :=
 match l with
 [ nil ⇒ false
 | cons h t ⇒ if (veqb e h) then true else (has_member t e)
 ]
 .
 
let rec rem_from_list l v on l ≝
 match l with
 [ nil ⇒ nil Variable
 | cons h t ⇒ if (veqb h v) then (rem_from_list t v) else (cons Variable h (rem_from_list t v))
 ]
 .
 
let rec rem_dup_var l on l ≝
 match l with
 [ nil ⇒ nil Variable
 | cons h t ⇒ cons Variable h (rem_from_list t h)
 ]
 .
 
 
let rec dom_list (e:Environment) on e ≝ 
 match e with
 [ Epsilon ⇒ []
 | Cons e s ⇒ if (has_member (dom_list e) (var_from_subst s)) then (dom_list e) else (cons Variable (var_from_subst s) (dom_list e))
 ]
 . 

let rec dom c ≝
 match c with
 [ CCrumble b e ⇒ dom_list e].
 
let rec l_subtr l1 l2 ≝
 match l1 with
 [ nil ⇒ nil Variable
 | cons h t ⇒ if (has_member l2 h) then t else cons Variable h (l_subtr t l2)
 ]
 .


let rec fv c ≝
 match c with
 [ CCrumble b e ⇒ rem_dup_var (append Variable (l_subtr (fv_byte b) (dom_list e)) (fv_env e))]

and

fv_env e ≝
 match e with
 [ Epsilon ⇒ nil Variable
 | Cons e s ⇒ match s with [subst x b ⇒ rem_dup_var (append Variable (rem_from_list (fv_env e) (x)) (fv_byte b))]
 ]
 
and

fv_val x ≝
 match x with
 [ var v ⇒ cons Variable v (nil Variable)
 | lambda v c ⇒ rem_from_list (fv c) v
 ]

and

fv_byte b ≝
 match b with
 [ CValue x ⇒ fv_val x
 | AppValue x y ⇒ rem_dup_var (append Variable (fv_val x) (fv_val y))
 ]
 .
 
let rec fresh_var e ≝
 match e with 
 [ Epsilon ⇒  O
 | Cons e' s ⇒  match s with [ subst v b ⇒ match v with [ variable n ⇒ max (S n) (fresh_var e')]]
 ]
 .

(*
let rec underline_pifTerm (t: pifTerm) :Crumble ≝
 match t with
 [ val_to_term v ⇒ 〈CValue (overline v), Epsilon〉
 | appl t1 t2 ⇒ match t2 with
                [ val_to_term v2 ⇒ match t1 with
                                   [ val_to_term v1 ⇒ 〈AppValue (overline v1) (overline v2), Epsilon 〉
                                   | appl u1 u2 ⇒ match underline_pifTerm t1 with [CCrumble b e ⇒ 〈AppValue (var ν(fresh_var e)) (overline v2), push e [ν(fresh_var e)←b]〉]
                                   ]
                | appl u1 u2 ⇒ match underline_pifTerm t2 with [ CCrumble b e ⇒ at (underline_pifTerm (appl t1 (val_to_term (pvar ν(fresh_var e))))) (push e [ν(fresh_var e)←b]) ]
                ]
 ]
*)

let rec underline_pifTerm (t: pifTerm):Crumble ≝
 match t with
 [ val_to_term v ⇒ CCrumble (CValue (overline v)) Epsilon
 | appl t1 t2 ⇒ match t2 with
                [ val_to_term v2 ⇒ match t1 with
                                   [ val_to_term v1 ⇒ 〈AppValue (overline v1) (overline v2), Epsilon〉
                                   | appl u1 u2 ⇒ match underline_pifTerm t1 with [ CCrumble b e ⇒ 〈AppValue (var ν(fresh_var e)) (overline v2), push e [(ν(fresh_var e)) ← b]〉]
                                   ]
                | appl u1 u2 ⇒ match underline_pifTerm t2 with [CCrumble b1 e1 ⇒ match t1 with
                                                                                     [ val_to_term v1 ⇒ at 〈AppValue (overline v1) (var ν(fresh_var e1)), Epsilon〉 (push e1 [ν(fresh_var e1)←b1])
                                                                                     | appl u1 u2 ⇒ match underline_pifTerm t1 with [CCrumble b e ⇒ 〈AppValue (var (ν(fresh_var e))) (var (ν(fresh_var e1))), concat (push e1 [ν(fresh_var e) ← b1]) (push e [ν(fresh_var e1) ← b])〉]
                                                                                     ]
                                                               ]
                ]
 ]

and
 
overline (x:pifValue): Value ≝
 match x with
 [ pvar v ⇒ var v
 | abstr v t ⇒ lambda (v) (underline_pifTerm t)
 ]
 .

let rec pif_subst t s ≝
 match t with
 [ val_to_term v ⇒ match v with [ pvar x ⇒ match s with [psubst v' t ⇒ match veqb v' x with [true ⇒ t | false ⇒ val_to_term v]]
                                | abstr x t1 ⇒ match s with [psubst v' t2 ⇒ match veqb v' x with [true ⇒ val_to_term v | false ⇒ val_to_term (abstr x (pif_subst t1 s))]]
                                ]
 | appl t' u ⇒  appl (pif_subst t' s) (pif_subst u s)
 ]
 .
 
let rec read_back x ≝
 match x with
 [ CCrumble b e ⇒ match e with
                  [ Epsilon ⇒ read_back_b b 
                  | Cons e1 s ⇒ match s with [ subst x b1 ⇒ pif_subst (read_back 〈b, e1〉) (psubst x (read_back_b b1))]]]
                  
and

read_back_b b ≝
 match b with
 [ CValue v ⇒ read_back_v v
 | AppValue v w ⇒ appl (read_back_v v) (read_back_v w)
 ]
 
and

read_back_v v ≝
 match v with
 [ var x ⇒ val_to_term (pvar x)
 | lambda x c ⇒ val_to_term (abstr x (read_back c))
 ]
 .