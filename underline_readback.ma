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

let rec has_member l (e:Variable) on l :=
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
 
let rec domb x c on c ≝
 match c with
 [ CCrumble b e ⇒ domb_e x e ]
 
and domb_e x e on e ≝
 match e with
 [ Epsilon ⇒ false
 | Cons e s ⇒ match s with [ subst y b ⇒ (veqb x y) ∨ (domb_e x e)]
 ]
 . 

 
let rec fvb x c on c : bool ≝ 
 match c with
 [ CCrumble b e ⇒ ((fvb_b x b) ∧ ¬(domb_e x e)) ∨ fvb_e x e ]

and fvb_b x b on b ≝ 
 match b with
 [ CValue v ⇒ fvb_v x v
 | AppValue v w ⇒ (fvb_v x v) ∨ (fvb_v x w)
 ]
 
and fvb_e x e on e ≝ 
 match e with
 [ Epsilon ⇒ false
 | Cons e s ⇒ match s with [subst y b ⇒ ((fvb_e y e) ∧ (¬ veqb x y)) ∨ fvb_b x b]
 ]
 
and fvb_v x v on v ≝ 
 match v with
 [ var y ⇒ veqb x y
 | lambda y c ⇒ (¬(veqb y x) ∧ fvb x c)
 ]
 .
 
let rec fresh_var c on c ≝
 match c with
 [ CCrumble b e ⇒  max (fresh_var_b b) (fresh_var_e e)]
 
and fresh_var_b b on b ≝
 match b with
 [ CValue v ⇒ fresh_var_v v
 | AppValue v w ⇒ max (fresh_var_v v) (fresh_var_v w)
 ]

and fresh_var_e e on e ≝ 
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒ max (fresh_var_e e) (fresh_var_s s) 
 ]

and fresh_var_v v on v ≝ 
 match v with
 [ var y ⇒ match y with [ variable x ⇒ S x ]
 | lambda y c ⇒ match y with [ variable x ⇒ max (S x) (fresh_var c)]
 ]
 
and fresh_var_s s on s ≝ 
 match s with
 [ subst x b ⇒ match x with [ variable x ⇒ max (S x) (fresh_var_b b)] ]
 .

let rec fresh_var_t t on t ≝
 match t with
 [ val_to_term v ⇒ fresh_var_tv v
 | appl v w ⇒ max (fresh_var_t v) (fresh_var_t w)
 ]

and fresh_var_tv v on v ≝
 match v with
 [ pvar v ⇒ match v with [variable x ⇒ S x]
 | abstr v t ⇒ match v with [variable x ⇒ max (S x) (fresh_var_t t)]
 ]
 .
(*
let rec fresh_var e ≝
 match e with 
 [ Epsilon ⇒  O
 | Cons e' s ⇒  match s with [ subst v b ⇒ match v with [ variable n ⇒ max (S n) (fresh_var e')]]
 ]
 .
  
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
(* deve restituire una coppia 〈crumble, numero di variabili già inserite〉 per usare il parametro destro sommato al numero di variabili presenti nel termine all'inizio per dare sempre una variabile fresca*)

let rec underline_pifTerm (t: pifTerm) (s: nat): Crumble × nat≝
 match t with
 [ val_to_term v ⇒ match overline v s with
   [ mk_Prod vv n ⇒  mk_Prod Crumble nat 〈(CValue vv), Epsilon 〉 n]
 | appl t1 t2 ⇒ match t2 with
   [ val_to_term v2 ⇒ match t1 with
     [ val_to_term v1 ⇒ match overline v1 s with 
       [ mk_Prod vv n ⇒ match overline v2 (s+n) with
         [ mk_Prod ww m ⇒ mk_Prod Crumble nat 〈AppValue (vv) (ww), Epsilon〉 (m+n) ]
       ]
     | appl u1 u2 ⇒ match underline_pifTerm t1 s with
       [ mk_Prod c n ⇒ match c with 
         [ CCrumble b e ⇒ match overline v2 (s+n) with 
           [ mk_Prod vv m ⇒ mk_Prod Crumble nat 〈AppValue (var ν(s+n+m)) (vv), push e [(ν(s+n)) ← b]〉 (S (n+m))]
         ]
       ]
     ]
   | appl u1 u2 ⇒ match underline_pifTerm t2 s with 
     [ mk_Prod c n ⇒ match c with
       [ CCrumble b1 e1 ⇒ match t1 with
         [ val_to_term v1 ⇒ match overline v1 (s+n) with
           [ mk_Prod vv m ⇒  mk_Prod Crumble nat (at 〈AppValue (vv) (var ν(s+n+m)), Epsilon〉 (push e1 [ν(s+n)←b1])) (S n)]
         | appl u1 u2 ⇒ match underline_pifTerm t1 (s+n) with
          [ mk_Prod c1 n1 ⇒ match c1 with
            [ CCrumble b e ⇒ mk_Prod Crumble nat 〈AppValue (var (ν(s+n+n1))) (var (ν(S(s+n+n1)))), concat (push e1 [ν(s+n+n1) ← b1]) (push e [ν(S(s+n+n1)) ← b])〉 (S (S (n + n1)))]
          ]
         ]
       ]
     ]
   ]
 ] 

and
 
overline (x:pifValue) (s: nat): Value × nat≝
 match x with
 [ pvar v ⇒ mk_Prod Value nat (var v) O
 | abstr v t ⇒ match underline_pifTerm t s with 
   [ mk_Prod c n ⇒ mk_Prod Value nat (lambda (v) (c)) n ]
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
(*
let rec c_size c on c ≝
 match c with
 [ CCrumble b e ⇒ c_size_b b + c_size_e e ]

and 

c_size_b b on b ≝
 match b with
 [ CValue v ⇒ c_size_v v
 | AppValue v w ⇒ c_size_v v + c_size_v w 
 ]

and

c_size_e e on e ≝
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒ S (c_size_e e) 
 ]
 
and

c_size_v v on v ≝
 match v with
 [ var x ⇒ O
 | lambda x c ⇒ c_size c
 ]
 .*)

let rec c_size c on c ≝
 match c with
 [ CCrumble b e ⇒ S (c_size_b b + c_size_e e) ]

and 

c_size_b b on b ≝
 match b with
 [ CValue v ⇒ c_size_v v
 | AppValue v w ⇒ S (c_size_v v + c_size_v w)  
 ]

and

c_size_e e on e ≝
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒(c_size_e e) + c_size_s s
 ]
 
and

c_size_v v on v ≝
 match v with
 [ var x ⇒ S O
 | lambda x c ⇒ S (c_size c)
 ]
 
and

c_size_s s on s ≝
 match s with
 [ subst x b ⇒ S (c_size_b b)]
 .
 
let rec c_len_e e on e ≝ match e with [Epsilon ⇒ O | Cons e s ⇒ 1 + c_len_e e].
 
let rec c_len c on c ≝
 match c with
 [ CCrumble b e ⇒ c_len_e e].
 
let rec e_pop e on e ≝ 
 match e with
 [ Epsilon ⇒ e
 | Cons e s ⇒ e
 ]
 .
 
let rec fv_pt x t on t≝
 match t with 
 [ val_to_term v ⇒ fv_pv x v
 | appl t1 t2 ⇒  orb (fv_pt x t1) (fv_pt x t2)
 ]
 
and fv_pv x v on v ≝ 
 match v with
 [ pvar y ⇒ veqb x y
 | abstr y t ⇒ if veqb x y then false else fv_pt x t
 ]
 .

lemma env_len: ∀e: Environment. (e = Epsilon → False ) →  S (c_len_e (e_pop e))=(c_len_e e).
#e cases e [ normalize #Abs cut False [ cut (Epsilon=Epsilon) [ //| @Abs] | #Abs
@False_ind] @Abs | #e1 #s #H1 normalize //] qed.

lemma succ_eq: ∀n, m:nat. S n = S m → n = m.
#n #m #H destruct // qed.

lemma subtr_1: ∀a,b,c:nat. a+b-(a+c)=b-c.
#a #b #c elim a // qed.

(* Definizione 1: naïve, restituisce il clasico errore: *)
(* NTypeChecker failure: Recursive call (read_back_b b), b is not smaller.

let rec read_back x on x ≝ 
 match x with
 [ CCrumble b e ⇒ match e with
                  [ Epsilon ⇒ read_back_b b 
                  | Cons e1 s ⇒ match s with [ subst x' b1 ⇒ pif_subst (read_back 〈b, e1〉) (psubst x' (read_back_b b1))]
                  ]
 ]                
 
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
*)

(* Definizione 2: come da lei consigliato, spezzo la read_back c in read_back b e *)
(* in modo che l'induzione su e mi assicuri la diminuzione della dimensione del termine*)
(* purtroppo però, la chiamata ricorsiva sul byte non mi assicura che la dimensione diminuisca*)
(* suppongo che questo sia dovuto al fatto che un byte può a sua volta contenere un  *)
(* crumble la cui dimensione è arbitraria *)


let rec aux_read_back rbb e on e ≝ 
 match e with
 [ Epsilon ⇒ rbb 
 | Cons e1 s ⇒ match s with [ subst x' b1 ⇒ pif_subst (aux_read_back rbb e1) (psubst x' (read_back_b b1))]
 ]                
 
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
 | lambda x c ⇒ match c with 
                [ CCrumble b e ⇒ val_to_term (abstr x (aux_read_back (read_back_b b) e))]
 ]
 .
 
let rec read_back c on c ≝
 match c with
 [ CCrumble b e ⇒ aux_read_back (read_back_b b) e]
 .

(* Definizione 3: ragionevolmente giusta, ma dà il seguente errore: read_back_b b *)
(* is not smaller. Faccio fatica a capirne il motivo, perché il fatto che la *)
(* lunghezza degli environment dei crumble di livello più esterno diminuisca ad *) 
(* ogni chiamata, dovrebbe assicurare la terminazione, ma suppongo anche *)
(* che Matita si aspetti che le chiamate per induzione sulla dimensione di *)
(* un termine abbiano come taglia un intero sempre decrescente, cosa che, con *)
(* la definizione di taglia data da c_len non si verifica. L'errore, dunque, *)
(* dovrebbe somigliare a quello del punto precedente.
*)

(*
let rec read_back (n: nat) : Πc: Crumble. c_len c = n → pifTerm ≝
 match n return λn.Πc: Crumble. c_len c = n → pifTerm with
 [ O ⇒ λc. match c return λc.c_len c = O → pifTerm with 
          [ CCrumble b e ⇒ λp.(read_back_b b)]
 | S m ⇒ λc. match c return λc.c_len c = S m → pifTerm with
    [ CCrumble b e ⇒ match e with 
        [ Epsilon ⇒  λabs.(read_back_b b) 
        | Cons e1 s ⇒ λp.match s with [ subst x' b1 ⇒ pif_subst (read_back m 〈b, e_pop e〉 ?) (psubst x' (read_back_b b1))]
        ]
    ]
 ]      

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
 | lambda x c ⇒ val_to_term (abstr x (read_back (c_len c) c (refl …))) 
 ]
 .

lapply p
normalize cases e normalize [ #H destruct | #e1 #s1 // ]
qed.
*)

(* Definizione 4: provo a definire una funzione size più accurata: la taglia *) 
(* di un crumble equivale alla lunghezza ti tutti gli environment in esso *)
(* annidati ney byte al primo membro. In questo modo dovrei riuscire ad evitare l'errore perché *)
(* la suddetta definizione mi garantirebbe la diminuzione della taglia del *) 
(* termine ad ogni chiamata ricorsiva. Ma quando vado a fornire la dimostrazione *)
(* mi si solleva un altro problema: come faccio ad esprimere il fatto che e = Cons e1 s ?
*)

(*
let rec read_back (n: nat) : Πc: Crumble. c_size c = n → pifTerm ≝
 match n return λn.Πc: Crumble. c_size c = n → pifTerm with
 [ O ⇒ λc.λabs. ?
 | S m ⇒ λc. match c return λc.c_size c = S m → pifTerm with
    [ CCrumble b e ⇒ match e return λe. c_size (CCrumble b e) = S m → pifTerm with 
        [ Epsilon ⇒  λp.(read_back_b (m) b (?))
        | Cons e1 s ⇒ match s return λs. c_size (CCrumble b (Cons e1 s)) = S m → pifTerm with [ subst x' b1 ⇒ λp. pif_subst (read_back ((S m) - (c_size_s [x'← b1])) 〈b, e1〉 ?) (psubst x' (read_back_b (m - c_size 〈b, e1〉) b1 ?))]
        ]
    ]
 ]
 

and

read_back_b (n: nat): Πb: Byte. c_size_b b = n → pifTerm ≝
 match n return λn.Πb: Byte. c_size_b b = n → pifTerm with
 [ O ⇒ λb. match b return λb. c_size_b b = O → pifTerm with
    [ CValue v ⇒ λp. read_back_v (c_size_v v) v (refl …)
    | AppValue v w ⇒ λabs. ?
    ]
 | S m ⇒ λb. match b return λb. c_size_b b = S m → pifTerm with
    [ CValue v ⇒ λp. read_back_v (c_size_v v) v (refl …)
    | AppValue v w ⇒ λp. appl (read_back_v (c_size_v v) v (refl …)) (read_back_v (c_size_v w) w (refl …))
    ]
 ]

and

read_back_v (n: nat): Πv: Value. c_size_v v = n → pifTerm≝
 match n return λn.Πv: Value. c_size_v v = n → pifTerm with
 [ O ⇒ λv. match v return λv. c_size_v v = O → pifTerm with
     [ var x ⇒ λp.val_to_term (pvar x)
     | lambda x c ⇒ λp.val_to_term (abstr x (read_back (c_size c) c (refl …))) 
     ]
 | S m ⇒ λv. match v return λv. c_size_v v = S m → pifTerm with
     [ var x ⇒ λp. val_to_term (pvar x)
     | lambda x c ⇒ λp. val_to_term (abstr x (read_back (c_size c) c (refl …))) 
     ]
 ]

 .
(*
[lapply p normalize cases (c_size_b b) [ normalize // | #n cases (c_size_e e1) [
#H // | #p #H cut (S ((S n)+(S p))=S m) [ // | @succ_eq] ] ]  qed.
*)
[ lapply abs cases c #b #e normalize cases (b) [ #v cases (v)[ #x normalize #abs
destruct | #x #d normalize #abs destruct] | #v #w normalize #abs destruct ] 
| lapply p normalize //
| normalize in p; destruct normalize cases (c_size_b b1)
 [ normalize // | #q normalize /2/]  
|  lapply p normalize #H destruct /2/
| normalize in abs; destruct] qed.
*)
(*
lemma value_lemma: ∀v: pifValue. read_back_v (overline v) = val_to_term v.
#v cases v
 [ #x normalize //
 | #x #t elim x #nx cases nx 
  [ normalize cases t [ normalize #v'   
*)
(*
lemma c4: ∀e: Environment. ∀x:Variable. ((has_member (dom_list e) x) = false)  → ((has_member (fv_env e) x) = false) → 
          ∀c: Crumble. ∀b: Byte. read_back (at c (push e [x←b]))= pif_subst (read_back (at c e)) (psubst x  (read_back 〈b, e〉)).
#e #x #H1 #H2 #c #b elim c
*)

definition ol ≝ λv. fst Value nat (overline v (fresh_var_tv v)).    
definition ul ≝ λt. fst Crumble nat (underline_pifTerm t (fresh_var_t t)).

lemma value_lemma: ∀v: pifValue. read_back_v (ol v) = val_to_term v.
#v @(pifValue_ind … v)
[ @(λt. (read_back (ul t) = t))
| #v0 #Hind normalize lapply Hind cases v0
 [ #x normalize //
 | #x #t normalize cases x normalize #n /2/  
|
| #x normalize //
| #t1 #x #Hind elim x #n elim n
 [ normalize lapply Hind cases t1
  [ normalize #v #H >H //
  | #t1 #t2 cases (t1) normalize  #H 




 #t1 #t2


