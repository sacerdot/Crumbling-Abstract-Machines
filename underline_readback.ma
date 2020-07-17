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
include "basics/types.ma".
include "libnat.ma".
include "variables.ma".
include "utils.ma".
include "size.ma".
include "pif_subst.ma".


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
           [ mk_Prod vv m ⇒ mk_Prod Crumble nat 〈AppValue (var ν(s+n+m)) (vv), push e [(ν(s+n+m)) ← b]〉 (S (s+n+m))]
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
            [ CCrumble b e ⇒ mk_Prod Crumble nat 〈AppValue (var (ν(s+n+n1))) (var (ν(S(s+n+n1)))), concat (push e1 [ν(s+n+n1) ← b1]) (push e [ν(S(s+n+n1)) ← b])〉 (S (S (s + n + n1)))]
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

definition ol ≝ λv. fst Value nat (overline v (fresh_var_tv v)).
definition ul ≝ λt. fst Crumble nat (underline_pifTerm t (fresh_var_t t)).

lemma size_lemma:
 (∀t.∀n. c_size (fst  … (underline_pifTerm t n)) ≤ 5 * (t_size t)) ∧
   (∀v.∀n. c_size_v (fst … (overline v n)) ≤ 5 * (v_size v)).

@pifValueTerm_ind
[ #v #H #s normalize lapply (H s) cases (overline v s) #w #n normalize //
| #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s lapply (H1 s) cases (overline v1 s) #vv #n normalize
      #H1' lapply (H2 (s+n)) cases (overline v2 (s+n)) #ww #m normalize #H2'
      lapply (le_plus … H1' H2') -H1' -H2' #H
      normalize in H1'; <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      cut ((c_size_v vv+c_size_v ww+O)≤(S (S (S (S
       (v_size v1+v_size v2
        +(v_size v1+v_size v2
          +(v_size v1+v_size v2+(v_size v1+v_size v2+(v_size v1+v_size v2+O))))))))))
      [ @le_S @le_S @le_S @le_S //
      | -H #H @le_S_S @H
      ]
    | #u1 #u2 normalize #H1 #H2 #s lapply (H1 s) normalize
      change with (underline_pifTerm (appl u1 u2) s) in match (match u2 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
              [val_to_term (v20:pifValue)⇒
               match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
               [val_to_term (v1:pifValue)⇒
                let 〈vv,n0〉 ≝overline v1 s in 
                let 〈ww,m〉 ≝overline v20 (s+n0) in 〈〈AppValue vv ww,Epsilon〉,m+n0〉
               |appl (u10:pifTerm)   (u20:pifTerm)⇒
                let 〈c,n0〉 ≝underline_pifTerm u1 s in 
                match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                [CCrumble (b:Byte)   (e:Environment)⇒
                 let 〈vv,m〉 ≝overline v20 (s+n0) in 
                 〈〈AppValue (var ν(s+n0+m)) vv,push e [ν(s+n0+m)←b]〉,S (s+n0+m)〉]]
              |appl (u10:pifTerm)   (u20:pifTerm)⇒
               let 〈c,n0〉 ≝underline_pifTerm u2 s in 
               match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
               [CCrumble (b1:Byte)   (e1:Environment)⇒
                match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                [val_to_term (v1:pifValue)⇒
                 let 〈vv,m〉 ≝overline v1 (s+n0) in 
                 〈〈AppValue vv (var ν(s+n0+m)),push e1 [ν(s+n0)←b1]〉,S n0〉
                |appl (u100:pifTerm)   (u200:pifTerm)⇒
                 let 〈c1,n1〉 ≝underline_pifTerm u1 (s+n0) in 
                 match c1 in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                 [CCrumble (b:Byte)   (e:Environment)⇒
                  〈〈AppValue (var ν(s+n0+n1)) (var ν(S (s+n0+n1))),
                   concat (push e1 [ν(s+n0+n1)←b1]) (push e [ν(S (s+n0+n1))←b])〉,
                  S (S (s+n0+n1))〉]]]]);
     cases (underline_pifTerm (appl u1 u2) s)
      * #b #e #n normalize lapply (H2 (s+n)) cases (overline v2 (s+n)) #vv #mm
      normalize #H2' #H1' <(size_env_push e  [ν(s+n+mm)←b])
      whd in match (c_size_e ?);
      whd in match (c_size_s ?);
      lapply (le_plus … H1' H2') -H1' -H2'
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      cut ((((((t_size u1+t_size u2
        +(t_size u1+t_size u2
          +(t_size u1+t_size u2+(t_size u1+t_size u2+(t_size u1+t_size u2+O)))))))))
   +(v_size v2+(v_size v2+(v_size v2+(v_size v2+(v_size v2+O))))) = (t_size u1+t_size u2+v_size v2
              +(t_size u1+t_size u2+v_size v2
                +(t_size u1+t_size u2+v_size v2
                  +(t_size u1+t_size u2+v_size v2
                    +(t_size u1+t_size u2+v_size v2+O))))))[ //] #HH <HH
       #H @le_S_S @le_S_S @le_S_S @le_S @le_S
       cut (c_size_v vv+(c_size_e e+c_size_b b)=c_size_b b+c_size_e e+(c_size_v vv+O)) [//]
       #HHH >HHH @H
       ]
  | #u1 #u2 normalize #H1 #H2 #s lapply (H2 s)
    change with (underline_pifTerm (appl u1 u2) ?) in match (match u2 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
              [val_to_term (v2:pifValue)⇒
               match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
               [val_to_term (v1:pifValue)⇒
                let 〈vv,n0〉 ≝overline v1 s in 
                let 〈ww,m〉 ≝overline v2 (s+n0) in 〈〈AppValue vv ww,Epsilon〉,m+n0〉
               |appl (u10:pifTerm)   (u20:pifTerm)⇒
                let 〈c,n0〉 ≝underline_pifTerm u1 s in 
                match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                [CCrumble (b:Byte)   (e:Environment)⇒
                 let 〈vv,m〉 ≝overline v2 (s+n0) in 
                 〈〈AppValue (var ν(s+n0+m)) vv,push e [ν(s+n0+m)←b]〉,S (s+n0+m)〉]]
              |appl (u10:pifTerm)   (u20:pifTerm)⇒
               let 〈c,n0〉 ≝underline_pifTerm u2 s in 
               match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
               [CCrumble (b1:Byte)   (e1:Environment)⇒
                match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                [val_to_term (v1:pifValue)⇒
                 let 〈vv,m〉 ≝overline v1 (s+n0) in 
                 〈〈AppValue vv (var ν(s+n0+m)),push e1 [ν(s+n0)←b1]〉,S n0〉
                |appl (u100:pifTerm)   (u200:pifTerm)⇒
                 let 〈c1,n1〉 ≝underline_pifTerm u1 (s+n0) in 
                 match c1 in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                 [CCrumble (b:Byte)   (e:Environment)⇒
                  〈〈AppValue (var ν(s+n0+n1)) (var ν(S (s+n0+n1))),
                   concat (push e1 [ν(s+n0+n1)←b1]) (push e [ν(S (s+n0+n1))←b])〉,
                  S (S (s+n0+n1))〉]]]]);
    cases (underline_pifTerm (appl u1 u2) s) * #b #e #n normalize
    lapply (H1 (s+n)) cases t1
    [ #v1 normalize cases (overline v1 (s+n)) #vv #m normalize
      <(size_env_push e  [ν(s+n)←b])
      whd in match (c_size_e (Cons e ?));
      whd in match (c_size_s ?);
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      #H1' #H2'
      @le_S_S @le_S_S @le_S_S @le_S @le_S
      lapply (le_plus …H1' H2') -H1' -H2' #H
      cut (v_size v1+(v_size v1+(v_size v1+(v_size v1+(v_size v1+O))))
    +S
     (S
      (S
       (S
        (S
         (t_size u1+t_size u2
          +(t_size u1+t_size u2
            +(t_size u1+t_size u2+(t_size u1+t_size u2+(t_size u1+t_size u2+O)))))))))=
   (S
    (S
     (S
      (S
       (S (v_size v1+(t_size u1+t_size u2))
        +(v_size v1+(t_size u1+t_size u2)
          +(v_size v1+(t_size u1+t_size u2)
            +(v_size v1+(t_size u1+t_size u2)
              +(v_size v1+(t_size u1+t_size u2)+O))))))))))
   [ <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
     @eq_f @eq_f @eq_f @eq_f @eq_f //
   | #HH <HH >commutative_plus in match (c_size_e e+c_size_b b); @H
   ]
  | #r1 #r2 cases (underline_pifTerm (appl r1 r2) (s+n)) * #b1 #e1 #n1 normalize
    >(size_env_concat  (push e [ν(s+n+n1)←b]) (push e1 [ν(S (s+n+n1))←b1]))
    <(size_env_push e  [ν(s+n+n1)←b])
    <(size_env_push e1 [ν(S(s+n+n1))←b1])
    whd in match (c_size_e (Cons e ?));
    whd in match (c_size_e (Cons e1 ?));
    whd in match (c_size_s ?);
    whd in match (c_size_s ?);
    #H1' #H2'
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    @le_S_S @le_S_S @le_S_S @le_S_S @le_S_S
    lapply (le_plus … H1' H2')
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    cut  (S
   (S
    (S
     (S
      (S
       (S
        (S
         (S
          (S
           (S
            (t_size r1+t_size r2
             +(t_size r1+t_size r2
               +(t_size r1+t_size r2
                 +(t_size r1+t_size r2+(t_size r1+t_size r2+O)))))))))
        +(t_size u1+t_size u2
          +(t_size u1+t_size u2
            +(t_size u1+t_size u2+(t_size u1+t_size u2+(t_size u1+t_size u2+O))))))))))=
  S
    (S
     (S
      (S
       (S
        (S
         (S
          (S
           (S
            (S (t_size r1+t_size r2+(t_size u1+t_size u2))
             +(t_size r1+t_size r2+(t_size u1+t_size u2)
               +(t_size r1+t_size r2+(t_size u1+t_size u2)
                 +(t_size r1+t_size r2+(t_size u1+t_size u2)
                   +(t_size r1+t_size r2+(t_size u1+t_size u2)+O))))))))))))))
   [@eq_f @eq_f @eq_f @eq_f @eq_f normalize //]
   #HH >HH #H
   cut (c_size_e e+c_size_b b+(c_size_e e1+c_size_b b1)=c_size_b b1+c_size_e e1+(c_size_b b+c_size_e e))
   [ // ] #Yee >Yee @H
   ]
 ]
| #x normalize //
| #p #v whd in match (overline ? ?);
  #H cut (t_size p+(t_size p+(t_size p+(t_size p+(t_size p+O))))≤
     (t_size p+S (t_size p+S (t_size p+S (t_size p+S (t_size p+O))))))
  [ <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm @le_S @le_S @le_S @le_S  //
  | #H2 #n normalize lapply (H n) cases (underline_pifTerm p n) #c #n normalize -H #H @le_S_S  @(transitive_le … H H2)
] qed.


lemma fv_lemma:
 (∀c.∀x. fvb_t x (read_back c) = true → fvb x c = true) ∧
  (∀b.∀x. fvb_t x (read_back_b b) = true → fvb_b x b = true ) ∧
   (∀e.∀b.∀x. (fvb_t x (read_back_b b)  = true → fvb_b x b = true) → fvb_t x (read_back 〈b, e〉) = true → fvb x 〈b, e〉  = true ) ∧
    (∀v.∀x. fvb_t x (read_back_v v) = true → fvb_v x v = true) ∧
     (∀s.∀b.∀e.∀x. (fvb_t x (read_back 〈b, e〉) = true → fvb x 〈b, e〉 = true ) →  fvb_t x (read_back 〈b, (Cons e s)〉)=true → fvb x 〈b, (Cons e s)〉=true).

@Crumble_mutual_ind
[ #b #e #H1 #H2 #x lapply (H1 x) lapply (H2 b x) #H @H
| #v #H assumption
| #v #w #H1 #H2 #x #H normalize in H;
  change with (appl (read_back_v v) (read_back_v w)) in match (read_back_b ?);
  change with (orb ? ?) in match (if ? then ? else ?) in H;
  whd in match (fvb_t ? ?);
  whd in match (free_occ_t ? ?);
  cut (fvb_t x (read_back_v v)=true ∨ fvb_t x (read_back_v w)=true)
   [ normalize lapply (gtb_O_true … H) #He elim He #j -He
     cases (free_occ_t x (read_back_v v))
     cases (free_occ_t x (read_back_v w))
     [ normalize #abs destruct
     | 2,3,4:  normalize /2/
     ]
   | * #Hrb  change with (fvb_v x v ∨ ?) in match (fvb_b ? ?);
     [ >(H1 x Hrb) //
     | >(H2 x Hrb) /2/
     ]
   ]
| #x #y normalize cases (veqb y x) normalize /2/
| #x #c cases c #b #e normalize #H #y lapply (H y) >(veqb_comm y x) elim (veqb x y) normalize
 [ #Hinutile  // | #Hutile @Hutile]
| #b #x normalize #H #H1 lapply (H H1) #H2 >H2 normalize //
| #e #s cases s #y #b' #H1 #H2 #b #x #H3 lapply (H1 b x) lapply (H2 b e x) #H1' #H2'
  lapply (H2' H3) #H4 lapply(H1' H4) -H1' normalize @sigma_prop_gen #z #_ * #_ #z_prop >z_prop
  <veqb_simm cut (veqb x y=true ∨ veqb x y = false) // * #Htf >Htf normalize
  #Hue #Hyee @(Hue Hyee)
| #y #b #H #b' #e #x
   cases y #ny lapply (H x) #Hx #H1
  whd in match (fvb ? ?); change with (orb ? ?) in match ( if ? then ? else ?);
  change with (aux_read_back ? ?) in match (read_back 〈b',Cons e [νny←b]〉);
  change with (pif_subst (aux_read_back (read_back_b b') e) ?)
    in match (aux_read_back (read_back_b b') (Cons e [νny←b]));
  change with (pi1 … (pif_subst_sig ? ? ? ?))
    in match (pif_subst (aux_read_back (read_back_b b') e) (psubst (νny) (read_back_b b)));
  @sigma_prop_gen #z #_ * #_ #z_prop
  change with (gtb ? ?) in match (fvb_t ? ?);
  change with (gtb ? ?) in match (fvb_t x z);
  normalize in match (fvb ? ?);
  >(z_prop x)
   whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
    whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
   change with (read_back 〈b', e〉) in match (aux_read_back (read_back_b b') e);
   change with (gtb (free_occ_t y (read_back_b b)) 0) in match (fvb_t y (read_back_b b)) in Hx;
   change with (gtb (free_occ_t y (read_back 〈b',e〉)) 0) in match (fvb_t y (read_back 〈b',e〉)) in H1;
   whd in match (domb_e ? ?); whd in match (fvb_e ? ?);
   lapply (H x) lapply H1;
   change with (gtb ? ?) in match (fvb_t ? ?);
   change with (gtb ? ?) in match (fvb_t x (read_back_b b));
   cases (free_occ_t x (read_back_b b)) cases (free_occ_t x (read_back 〈b',e〉))
   [ normalize cut ( free_occ_t (νny) (aux_read_back (read_back_b b') e)*O+O=0)
     [ cases  (free_occ_t (νny) (aux_read_back (read_back_b b') e)) //
     | #H0 >H0 >if_monotone whd in match (gtb 0 0); #abs #_ #abs destruct
     ]
   |  #n #Hyess normalize in Hyess; <veqb_simm cut (veqb x (νny)=true ∨ veqb x (νny)=false) // * #Htf
     [ >Htf normalize >if_then_false_else_false >if_then_false_else_false
       normalize >times_O normalize #_ #abs destruct
     | change with (orb ? ?) in match (if veqb x (νny) then true else domb_e x e);
       change with (orb ? ?) in match (if (fvb_e (νny) e∧¬veqb x (νny)) then true else fvb_b x b);
       >Htf change with (domb_e x e) in match (false∨domb_e x e);
       change with true in match (¬false);
       normalize >times_O normalize #_
       change with (notb ?) in match (if domb_e x e then false else true);
       change with (andb ? ?) in match (if fvb_b x b' then (¬domb_e x e) else false);
       >if_then_true_else_false
       change with (orb ? ?) in match (if fvb_e (νny) e then true else fvb_b x b);
       change with (orb ? ?) in match (if ? then ? else ?); #_
       change with (notb ?) in match (if domb_e x e then false else true) in Hyess;
       change with (andb ? ?) in match (if fvb_b x b' then (¬domb_e x e) else false) in Hyess;
       change with (orb ? ?) in match (if ?then ? else ?)in Hyess;
       cut ((fvb_b x b'∧¬domb_e x e∨fvb_e x e)=true)
       [ @Hyess //
       | -Hyess #H4
         cut ((fvb_b x b'∧¬domb_e x e)=true∨fvb_e x e=true)
         [ lapply H4 cases fvb_b cases fvb_e cases domb_e
           normalize /2/
         | * -H4 #H4 >H4 normalize //
         ]
       ]
     ]
   | normalize #H3 #H_ #H5 >H5 // >if_monotone >if_monotone #_ //
   | #n #m normalize #_ #H5 >H5 // >if_monotone >if_monotone #_ //
   ]
] qed.


(*
lemma pif_subst_distro:
 (∀t.∀x, t'. fresh_var_t (pif_subst t (psubst (νx) t')) ≤
  max (fresh_var_t t) (fresh_var_t t')) ∧
 ∀v. (∀x, t'. fresh_var_t (pif_subst (val_to_term v) (psubst (νx) t')) ≤
  max (fresh_var_tv v) (fresh_var_t t')).

@pifValueTerm_ind
[ #v #H cut (∀v. fresh_var_tv v=fresh_var_t (val_to_term v)) //
| #t1 #t2 #H1 #H2 #x #t' >pif_subst_distro
  change with (max (fresh_var_t (pif_subst t1 (psubst (νx) t'))) (fresh_var_t (pif_subst t2 (psubst (νx) t'))))
    in match (fresh_var_t ?);
  cut (max (fresh_var_t (pif_subst t1 (psubst (νx) t')))
           (fresh_var_t (pif_subst t2 (psubst (νx) t')))
       ≤ max (max (fresh_var_t t1) (fresh_var_t t'))
             (max (fresh_var_t t2) (fresh_var_t t')))
  [ @(to_max)
    [ @(le_le_max …) @H1
    | >max_comm @(le_le_max …) @H2
    ]
  |#H change with (max (fresh_var_t t1) (fresh_var_t t2)) in match (fresh_var_t (appl t1 t2));
  <max_fact @H
  ]
| #x #ny #t' cases x #nx cut (veqb (νnx) (νny)=true ∨ veqb (νnx) (νny)=false) // *
  #Htf
  [ lapply (veqb_true_to_eq (νnx) (νny)) * #Heq #_ lapply (Heq Htf) destruct
    -Htf -Heq #Heq destruct >atomic_subst >max_comm
    cut (fresh_var_t t'≤ max ny (fresh_var_t t'))
    [ >max_comm @le_n_max_n
    | #H @(le_le_max …) //
    ]
  | >no_subst //
  ]
| #t #x #H #y #t' lapply (H y t') -H #H
  change with (pi1 … (pif_subst_sig ? ? ? ?)) in match ( pif_subst ? ?);
*)
lemma fresh_var_lemma:
 (∀c. fresh_var_t (read_back c) ≤ fresh_var c) ∧
  (∀b. fresh_var_t (read_back_b b) ≤ fresh_var_b b ) ∧
   (∀e.∀b. (fresh_var_t (read_back_b b) ≤ fresh_var_b b) → fresh_var_t (read_back 〈b, e〉) ≤ fresh_var 〈b, e〉) ∧
    (∀v. fresh_var_t (read_back_v v) ≤ fresh_var_v v) ∧
     (∀s.∀b.∀e. (fresh_var_t (read_back 〈b, e〉) ≤ fresh_var 〈b, e〉) →  fresh_var_t (read_back 〈b, (Cons e s)〉) ≤ fresh_var 〈b, (Cons e s)〉).

@Crumble_mutual_ind
[ #b #e #H #H1 @(H1 b H)
| #v #H whd in match (fresh_var_b (CValue v)); whd in match (read_back_b ?); @H
| #v #w #H1 #H2 whd in match (fresh_var_b (AppValue ? ?));
  change with (max (fresh_var_v ?) (fresh_var_v ?))
   in match (if leb (fresh_var_v v) (fresh_var_v w) then fresh_var_v w else fresh_var_v v);
  whd in match (read_back_b ?);
  change with (max (fresh_var_t (read_back_v v)) (fresh_var_t (read_back_v w))) in match (fresh_var_t ?);
  @(to_max … )
  [ whd in match (max ? ?);
    cut (leb (fresh_var_v v) (fresh_var_v w)=true ∨ leb (fresh_var_v v) (fresh_var_v w)=false) //
    * #Htf >Htf
    [ change with (fresh_var_v w) in match (if true then (fresh_var_v w) else ?);
      lapply (leb_true_to_le … Htf) -Htf #H @(transitive_le … H1 H)
    | change with (fresh_var_v v) in match (if false then ? else (fresh_var_v v));
      @H1
    ]
  | whd in match (max ? ?);
    cut (leb (fresh_var_v v) (fresh_var_v w)=true ∨ leb (fresh_var_v v) (fresh_var_v w)=false) //
    * #Htf >Htf
    [ change with (fresh_var_v w) in match (if true then (fresh_var_v w) else ?);
      @H2
    | change with (fresh_var_v v) in match (if false then ? else (fresh_var_v v));
      lapply (leb_false_to_not_le … Htf) -Htf #H lapply (not_le_to_lt … H) -H #H
      lapply (lt_to_le … H) -H #H @(transitive_le … H2 H)
    ]
  ]
| #x cases x #nx normalize //
| #x cases x #nx #c cases c #b #e normalize
  cases (pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) (aux_read_back (read_back_b b) e)→S x0≤n)
  (fresh_var_t_Sig (aux_read_back (read_back_b b) e)))
  change with (fresh_var 〈b, e〉) in match ((if leb (fresh_var_b b) (fresh_var_e e) 
         then fresh_var_e e 
         else fresh_var_b b));
  [ #H whd in match (match ? in nat with [ _ ⇒ ? ]);
    change with (S nx) in match (if false then O else S nx );
    change with (leb (S nx) ?) in match (match fresh_var 〈b,e〉 in nat return λ_:ℕ.bool with 
        [O⇒false|S (q:ℕ)⇒leb nx q]);
    cut (leb (S nx) (fresh_var 〈b, e〉)=true ∨ leb (S nx) (fresh_var 〈b, e〉)=false) //
    | #k #H change with (leb (S nx) ?) in match (match fresh_var 〈b,e〉 in nat with 
    [O⇒false|S (q:ℕ)⇒leb nx q]);
    change with (leb (S nx) (S k)) in match (match (S k) in nat with 
    [O⇒false|S (q:ℕ)⇒leb nx q]);
    change with (max ? ?) in match (if ? then ? else ?);
    change with (max (S nx) (fresh_var 〈b, e〉)) in match (if (leb (S nx) (fresh_var ?)) then ? else ?);
    @(to_max …)
    change with (if (leb (S nx) (fresh_var 〈b, e〉)) then (fresh_var 〈b, e〉) else (S nx)) in match (max (S nx) ?);
    cut (leb (S nx) (fresh_var 〈b,e〉)=true ∨ leb (S nx) (fresh_var 〈b,e〉)=false) // * #Htf >Htf
    [ lapply (leb_true_to_le … Htf) -Htf #Hle
      change with (fresh_var 〈b,e〉) in match (if true then fresh_var 〈b,e〉 else S nx ); //
    | 3: normalize
    | lapply(leb_false_to_not_le … Htf) -Htf #Hnle
      lapply (not_le_to_lt … Hnle) -Hnle #Hlt
      lapply (lt_to_le … Hlt) -Hlt #Hle
      change with (S nx) in match (if ? then ? else ?);
      @(transitive_le … H Hle)
    ]
  ]
| #b #H whd in match (read_back ?); whd in match (fresh_var ?);
  whd in match (fresh_var_e Epsilon); lapply H cases (fresh_var_b …)
  normalize //
| #e #s #H1 #H2 #b #H @(H2 … (H1 … H))
| #x #b' #H #b #e #H1 cases x #nx lapply H1
  change with (max ? ?) in match (fresh_var 〈b, e〉);
  change with (max ? ?) in match (fresh_var 〈b, Cons ? ?〉);
  change with (max ? ?) in match (fresh_var_e (Cons e ?));
  change with (max ? ?) in match (fresh_var_s ?);
  whd in match (read_back ?);
  #H1'
  change with (pif_subst (aux_read_back (read_back_b b) e) ?)
  in match (read_back ?);
  normalize
  @sigma_prop_gen #z #z_def * #_ #z_prop
 whd in match (fresh_var_v ?);
  change with (max ? ?) in match (if ? then ? else ?);
  whd in match (read_back_v ?); lapply H cases c #b #e
  -H #H whd in match (match ? in Crumble with [ _ ⇒ ? ]);
*)

definition interval_dom ≝  λe, b. ∀x. domb_e (νx) e =true → b ≤ x.

lemma interval_lemma:  ∀x, e, s. interval_dom (Cons e s) x → interval_dom e x.
#x #e #s  @(Environment_simple_ind2 … e)
[ #H normalize #x #abs destruct
| cases s #y #t normalize #e' #s' elim y #ny normalize #H #H' #x0 lapply (H' x0)
  cases (neqb x0 ny)
  [ normalize #Htot #_ @Htot //
  | normalize #Htot @Htot
  ]
]
qed.

lemma interval_lemma2: ∀e. ∀ (y:Variable).∀ b, n. (interval_dom (Cons e [y←b]) n) → n ≤ match y with [variable ny ⇒ ny].
#e #y #b #n cases y #ny normalize #H @(H ny) lapply (neqb_iff_eq … ny ny) * #_
#Hscontata >Hscontata // qed.

lemma fresh_var_occ:
 (∀t. ∀x. x ≥ (fresh_var_t t) → free_occ_t (νx) t = 0) ∧
  (∀v. ∀x. x ≥(fresh_var_tv v) →  free_occ_v (νx) v = 0).

@pifValueTerm_ind
[ #v #H #x @H
| #t1 #t2 #H1 #H2 #x #H change with (max ? ?) in match (fresh_var_t ?) in H;
  cut (max (pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t1≥1→n>x0) (fresh_var_t_Sig t1))
    (pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t2≥1→n>x0) (fresh_var_t_Sig t2))≤x) //
  -H #H lapply(le_maxl … H) #H11 lapply(le_maxr … H) #H22 -H
  cut (x ≥pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t1≥1→n>x0) (fresh_var_t_Sig t1)) // -H11 #H11
  cut (x ≥pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t2≥1→n>x0) (fresh_var_t_Sig t2)) // -H22 #H22
  lapply (H1 … H11) lapply (H2 x H22) -H1 -H11 -H2 -H22 #H2 #H1
  change with (plus ? ?) in match (free_occ_t ? ?); //
| #x cases x #nx normalize #y #H cut (neqb y nx = true ∨ neqb y nx = false) // *
  #Htf [2: >Htf // | @False_ind lapply (neqb_iff_eq y nx) * #Heq #_ lapply (Heq Htf)
  -Htf -Heq #Heq destruct @(leq_Sx_x_false nx H)]
| #t #x #HI #y whd in match (fresh_var_tv ?); whd in match (fresh_var_tv_Sig ?);
  cases x #nx normalize
  change with (leb (S nx) ?) in match (match pi1 ℕ (λn:ℕ.∀x00:ℕ.1≤free_occ_t (νx00) t→S x00≤n) (fresh_var_t_Sig t)
        in nat
        return λ_:ℕ.bool
        with 
       [O⇒false|S (q:ℕ)⇒leb nx q]);
  change with (max ? ?) in match (if ? then ? else ?);
  #H lapply(le_maxl … H) #H1 lapply(le_maxr … H) #H2 -H
  cut (y≥(pi1 ℕ (λn:ℕ.∀x00:ℕ.1≤free_occ_t (νx00) t→S x00≤n) (fresh_var_t_Sig t))) //
  -H2 #H2 >(HI y H2) cases (neqb y nx) //
] qed.
(*
lemma pif_subst_lemma: ∀t, t', ny. fresh_var_t t ≤ ny → pif_subst t (psubst (νny) t')=t.
#t #t' #ny #H
change with (pi1 … (pif_subst_sig (t_size t) ? t ?)) in match (pif_subst ??);
@(nat_ind … (t_size t));
normalize () t @sigma_prop_gen cases (t_size t) #z #z_def * #_ #z_prop
*)

lemma fresh_var_abstr: ∀x,t,ny. fresh_var_t (val_to_term (abstr x t)) ≤ ny → veqb x (νny) =false.
#x #t #ny cut (veqb x (νny)=true ∨ veqb x (νny)=false) // * #Hveqb [2: //]
lapply (veqb_true_to_eq x (νny)) * #Heq #_ lapply (Heq Hveqb) -Hveqb -Heq #Heq
destruct >veqb_true normalize  change with (leb (S ny) ?) in match (match pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t→S x0≤n) (fresh_var_t_Sig t)
         in nat
         return λ_:ℕ.bool
         with 
        [O⇒false|S (q:ℕ)⇒leb ny q])  ;
        change with (max ? ?) in match (if ? then ? else ?);
#H lapply(le_maxl … H) #abs -H @False_ind /2/ qed.

lemma aux_read_back1: ∀t1, t2, e. aux_read_back (appl t1 t2) e = appl (aux_read_back t1 e) (aux_read_back t2 e).
#t1 #t2 #e @(Environment_simple_ind2 … e)
[ normalize //
| #e' #s cases s #x #b
  change with (pif_subst (aux_read_back (appl t1 t2) e') (psubst x (read_back_b b)))
  in match (aux_read_back (appl t1 t2) (Cons e' [x←b]));
  change with (pif_subst (aux_read_back t1 e') (psubst x (read_back_b b)))
  in match (aux_read_back t1 (Cons e' [x←b]));
  change with (pif_subst (aux_read_back t2 e') (psubst x (read_back_b b)))
  in match (aux_read_back t2 (Cons e' [x←b]));
  #HI >HI @pif_subst_distro
] qed.

lemma push_lemma_aux: ∀t, e, s. aux_read_back t (Cons e s) = aux_read_back (aux_read_back t e) (Cons Epsilon s).
#t #e @(Environment_simple_ind2 … e)
[ #s normalize in match ((aux_read_back t Epsilon)); //
| #e' #s' #H #s lapply (H s')
 cases s' #y #b #H' >H' /2/
]. qed.


lemma push_lemma:
 ∀t, e, s. aux_read_back t (push e s) = aux_read_back (pif_subst t match s with [subst x b ⇒ psubst x (read_back_b b) ]) e.
 #t #e @(Environment_simple_ind2 … e)

[ normalize #s cases s #x #b normalize //
| #e' #s' #H #s lapply (H s)
  normalize in match (push ? ?) in ⊢ (? → %);
  cases s #y #t
  normalize in match (match [y←t]  with 
    [subst (x:Variable)   (b:Byte)⇒psubst x (read_back_b b)]);
  #H' >(push_lemma_aux …) /2/
] qed.

lemma fresh_dom_e: ∀x, e. domb_e (νx) e =true → x ≤ fresh_var_e e.
#x #e @(Environment_simple_ind2 … e)
[ normalize #abs destruct
| #e' * * #ny #b normalize change with (leb (S ny) ?) in match (match fresh_var_b b in nat with 
                [O⇒false|S (q:ℕ)⇒leb ny q]);
  change with (max ? ?) in match (if leb ? ? then ? else ? );
  change with (max ? ?) in match (if leb (S ny) ? then ? else ? );
  cut (neqb x ny=true ∨ neqb x ny=false) // * #Htf >Htf
  [ >if_t lapply (neqb_iff_eq … x ny) * #Heq #_ lapply (Heq Htf) -Heq
    #Heq destruct #_ #_ >max_comm cut (ny ≤S ny) // #Hw
    cut (S ny≤max (max (S ny) (fresh_var_b b)) (fresh_var_e e'))
    [ /2/
    | #H @le_le_max cut (S ny ≤max (S ny) (fresh_var_b b))[ @le_n_max_n | #HH @le_le_max assumption]
    ]
  | >if_f #H #HH lapply (H HH) -H -HH #H @le_le_max assumption
  ]
qed.
axiom pif_subst_lemma: ∀ny.
 (∀t. fresh_var_t t ≤ ny → ∀t'. pif_subst t (psubst (νny) t')=t).

(*
il lemma seguente non è dimostrabile in questa formulazione perché la pif_subst
effettua α-conversioni anche senza che avvenga la sostituzione,
l'uguaglianza fra un termine ed il suo sostituito è dunque vera se intesa come
equivalenza a meno di α-conversioni
*)

(*
lemma pif_subst_lemma: ∀ny.
 (∀t. fresh_var_t t ≤ ny → ∀t'. pif_subst t (psubst (νny) t')=t) ∧
  ∀v. fresh_var_tv v ≤ ny →∀t'. pif_subst (val_to_term v) (psubst (νny) t')=(val_to_term v).

#ny @pifValueTerm_ind
[ 3: #x #H #t' whd in match (pif_subst_sig  ? ? ? ? );
  cut (∀gg.∀ tt. (pi1 pifTerm
  (λu:pifTerm
   .t_size u
    =(t_size (val_to_term (pvar x)))
     +((free_occ_t (νny) (val_to_term (pvar x)))*(t_size t'-1))
    ∧(∀z:Variable
      .free_occ_t z u
       =if match z in Variable return λ_:Variable.bool with 
             [variable (m1:ℕ)⇒neqb ny m1] 
        then (free_occ_t z (val_to_term (pvar x)))*(free_occ_t z t') 
        else (free_occ_t (νny) (val_to_term (pvar x)))*(free_occ_t z t')
                 +free_occ_t z (val_to_term (pvar x)) ))
 (match veqb (νny) x
 return λb. veqb (νny) x = b → 1 ≤ 1 →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb (νny) x = true.
        λp: 1 ≤ 1.
         «t', gg H p»
     | false ⇒ λH: veqb (νny) x = false.
        λp: 1 ≤ 1.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb (νny) x )) (le_n 1))) = val_to_term (pvar x))
     [2: #UU @UU]  #gg #tt
     lapply (fresh_var_occ) * #fv_occ #_
     cut (free_occ_t (νny) (val_to_term (pvar x))=0)
     [ @fv_occ //
     | cut (veqb (νny) x=true ∨ veqb (νny) x=false ) // *
     #Hveqb
     [ lapply (veqb_true_to_eq (νny) x) * #Heq #_
       lapply (Heq Hveqb) -Heq #Heq destruct #abs
       normalize in abs; normalize in Hveqb;>Hveqb in abs;
       #abs normalize in abs; destruct
     | >Hveqb in gg tt ⊢ %; normalize #_ #_ #_ //
     ]
   ]
| 4: #r #x #HI #H #t' whd in match (pif_subst_sig  ? ? ? ? );
  whd in match (match ? in pifSubst with [_ ⇒ ?]);
  whd in match (match ? in pifSubst with [_ ⇒ ?]);
  cut (∀K.∀K1.∀K2. (pi1 pifTerm   (λu:pifTerm
   .t_size u
    =(t_size (val_to_term (abstr x r)))
     +(free_occ_t (νny) (val_to_term (abstr x r)))*(t_size t'-1)
    ∧(∀z:Variable
      .free_occ_t z u
       =if match z in Variable return λ_:Variable.bool with 
             [variable (m1:ℕ)⇒neqb ny m1] 
        then (free_occ_t z (val_to_term (abstr x r)))*(free_occ_t z t' )
        else (free_occ_t (νny) (val_to_term (abstr x r)))*(free_occ_t z t')
                 +(free_occ_t z (val_to_term (abstr x r))) ))
  (match veqb (νny) x return λb. veqb (νny) x = b → t_size (val_to_term (abstr x r)) ≤ S (t_size r) → Σu: pifTerm. ?
      with
       [ true ⇒ λH:veqb (νny) x = true.λp:t_size (val_to_term (abstr x r)) ≤ S (t_size r). «(val_to_term (abstr x r)), K H p »
       | false ⇒ λH:veqb (νny) x = false. match fvb_t x t'return λb. fvb_t x  t' = b → t_size (val_to_term (abstr x r)) ≤ S (t_size r) → Σu: pifTerm. ?
        with
         [ true ⇒ λHH:fvb_t x  t' = true. λp:t_size (val_to_term (abstr x r)) ≤ S (t_size r). let z ≝ (max (S ny) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t r) (fresh_var_t t'))))
                  in match (pif_subst_sig (t_size r) (psubst x (val_to_term (pvar ν(z)))) r (le_n ?)) with
           [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size r) (psubst (νny) t') a (subst_aux_5 r x z a (t_size r) h p))))), K1 H HH p a h »]
         | false ⇒ λHH:fvb_t x  t' = false. λp. «(val_to_term (abstr x (pi1 … (pif_subst_sig (t_size r) (psubst (νny) t') r (le_n ?))))), K2 H HH p»
         ] (refl …)
       ] (refl bool (veqb (νny) x)) (le_n (t_size (val_to_term (abstr x r)))))=val_to_term (abstr x r)))
       [2: #UU @UU] #K #K1 #K2
       lapply (fresh_var_occ) * #fv_occ #_
     cut (free_occ_t (νny) (val_to_term (abstr x r))=0)
     [@fv_occ //
     | lapply(fresh_var_abstr …H) #Hveqb  check veqb_comm lapply (veqb_comm x (νny)) #Hcomm <Hcomm in K K1 K2 ⊢ %;
        #K #K1 #K2 >Hveqb in K K1 K2 ⊢ %; lapply (fresh_var_abstr_decr x r) #Hm
        lapply (HI (transitive_le … Hm H)) -HI #HI  #K #K1 #K2
        cut (fvb_t x t'=true ∨ fvb_t x t'=false) // * #Hfvb_t >Hfvb_t in K K1 K2 ⊢ %;
        [ 2:  #K #K1 #K2 #FreeOcc normalize in HI; normalize @eq_f @eq_f @HI
        | #K #K1 #K2 #Hfo whd in match (pi1 …); normalize >HI
        change with (pif_subst r (psubst (νny) t')) in match (pif_subst_sig (t_size r) (psubst (νny) t') r
                                 (le_n (t_size r))); normalize in HI;
        cut (∀K. (pi1 pifTerm
   (λu:pifTerm
    .t_size u=t_size r+(free_occ_t (νny) r)*(t_size t'-1)
     ∧(∀z:Variable
       .free_occ_t z u
        =if match z in Variable return λ_:Variable.bool with 
              [variable (m1:ℕ)⇒neqb ny m1] 
         then (free_occ_t z r)*(free_occ_t z t') 
         else (free_occ_t (νny) r)*((free_occ_t z t')+(free_occ_t z r)) ))
   (pif_subst_sig (t_size r) (psubst (νny) t') r (K (t_size r)))
   =r));


         >HI in K K1 K2 ⊢ %; normalize // check veqb_comm normalize #_ #_ #_ //
     ]




      >Hfv_occ in K K1 K2 ⊢ %;
*)

lemma aux_read_back3: ∀t, e, b.
  (fresh_var_t t ≤ b) →
   (interval_dom e b) → (*interval_dom ≝  λe, b. ∀x. domb_e (νx) e =true → b ≤ x.*)
     aux_read_back t e = t.

#t #e #b #H1
@(Environment_simple_ind2 … e)
[ normalize //
| #e' #s' #HI #H1 lapply (HI (interval_lemma … H1)) #H2
  lapply H1 cases s' #y #b' -H1 #H1
  change with (pif_subst (aux_read_back t e') (psubst y (read_back_b b')))
  in match (aux_read_back t (Cons e' [y←b'])) ; >H2
  lapply (interval_lemma2 … e' y b' b H1) cases y #ny #Hforte
  normalize in Hforte; @pif_subst_lemma /2/
]. qed.


(*
lemma basic_subst: ∀x, t. (pif_subst (val_to_term (pvar x)) (psubst x t)) = t.
#x #t change with (pi1 … (pif_subst_sig (t_size ?) ? ? ?)) in match (pif_subst ??);
change with (1) in match (t_size (val_to_term (pvar x)));
whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
whd in match (pif_subst_sig 1 (psubst x t) (val_to_term (pvar x)) (le_n 1));
lapply(veqb_true x) #Ht cases (veqb x x)
*)

lemma four_dot_two:
    (∀t.∀s. (s ≥ fresh_var_t t) → read_back (fst ?? (underline_pifTerm t s)) = t ∧
      (snd ?? (underline_pifTerm t s) + s ≥ (fresh_var (fst ?? (underline_pifTerm t s))))) ∧
    (∀v.∀s. (s ≥ fresh_var_tv v) →read_back_v (fst ?? (overline v s)) = val_to_term v ∧
      ((snd ?? (overline v s)) + s ≥ fresh_var_v (fst ?? (overline v s)))).

@(pifValueTerm_ind (λt.∀s. (s ≥ fresh_var_t t) → read_back (fst ?? (underline_pifTerm t s)) = t ∧
      (snd ?? (underline_pifTerm t s) + s ≥ (fresh_var (fst ?? (underline_pifTerm t s)))))
      (λv.∀ s. (s ≥ fresh_var_tv v) →read_back_v (fst ?? (overline v s)) = val_to_term v ∧
      ((snd ?? (overline v s)) + s ≥ fresh_var_v (fst ?? (overline v s)))))
[ #v normalize in match (fresh_var_tv ?); @sigma_prop_gen #z #z_def #z_prop #HI #s #Hsz lapply (HI s Hsz)
 -HI -Hsz * normalize cases (overline v s) #vv #nn normalize #H1 #H2 % // lapply H2
 cases (fresh_var_v vv) normalize //
| #t1 #t2 cases t2
  [ #v2 cut (t1=t1) // #Ht1
    cases t1
    [ #v1 normalize @sigma_prop_gen #zv1 #zv1_def #zv1_prop @sigma_prop_gen #zv2 #zv2_def #zv2_prop #H1 #H2
      #s lapply (H1 s) cases (overline v1 s) #vv #n -H1 #H1 normalize lapply (H2 (s+n))
      cases (overline v2 (s+n)) #ww #m -H2 #H2 change with (max ? ?) in match (if ? then ? else ?);
      #Hmax lapply (le_maxl … Hmax) lapply (le_maxr … Hmax) -Hmax lapply H2 lapply H1
      normalize -H1 -H2 #H1 #H2 #Hzv2 #Hzv1 cut (zv2≤s+n) /2/ -Hzv2 #Hzv2
      lapply (H2 Hzv2) lapply (H1 Hzv1) -H1 -H2 #H1 #H2
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max (max ? ?) ?) in match (max (if leb ? ? then ? else ?) ?);
      change with (max ? ?) in match (if ? then ? else ?) in H1;
      change with (max ? ?) in match (if ? then ? else ?) in H2;
      >(max_O ?) >(max_O ?) in H2; >(max_O ?) in H1; * #H1a #H1b * #H2a #H2b
      >H1a >H2a % // @(to_max …) /2/
      #s
    | #u1 #u2 normalize @sigma_prop_gen #zu1 #zu1_def #zu1_prop normalize @sigma_prop_gen #zu2 #zu2_def #zu2_prop
      @sigma_prop_gen #zv2 #zv2_def #zv2_prop normalize #Hu1u2 #Hv2 #s lapply (Hu1u2 s)
      change with (underline_pifTerm (appl u1 u2) s) in match
      (match u2 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                 [val_to_term (v20:pifValue)⇒
                  match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                  [val_to_term (v1:pifValue)⇒
                   let 〈vv,n〉 ≝overline v1 s in 
                   let 〈ww,m〉 ≝overline v20 (s+n) in 〈〈AppValue vv ww,Epsilon〉,m+n〉
                  |appl (u10:pifTerm)   (u20:pifTerm)⇒
                   let 〈c,n〉 ≝underline_pifTerm u1 s in 
                   match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                   [CCrumble (b:Byte)   (e:Environment)⇒
                    let 〈vv,m〉 ≝overline v20 (s+n) in 
                    〈〈AppValue (var ν(s+n+m)) vv,push e [ν(s+n+m)←b]〉,S (s+n+m)〉]]
                 |appl (u10:pifTerm)   (u20:pifTerm)⇒
                  let 〈c,n〉 ≝underline_pifTerm u2 s in 
                  match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                  [CCrumble (b1:Byte)   (e1:Environment)⇒
                   match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                   [val_to_term (v1:pifValue)⇒
                    let 〈vv,m〉 ≝overline v1 (s+n) in 
                    〈〈AppValue vv (var ν(s+n+m)),push e1 [ν(s+n)←b1]〉,S n〉
                   |appl (u100:pifTerm)   (u200:pifTerm)⇒
                    let 〈c1,n1〉 ≝underline_pifTerm u1 (s+n) in 
                    match c1 in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                    [CCrumble (b:Byte)   (e:Environment)⇒
                     〈〈AppValue (var ν(s+n+n1)) (var ν(S (s+n+n1))),
                      concat (push e1 [ν(s+n+n1)←b1]) (push e [ν(S (s+n+n1))←b])〉,
                     S (S (s+n+n1))〉]]]]);
        cases (underline_pifTerm (appl u1 u2) s) #c #n -Hu1u2 lapply (Hv2 (s+n))
        normalize cases c #b #e cases (overline v2 (s+n)) #vv #m normalize
        change with (max ? ?) in match (if leb ? ? then ?  else ?);
        change with (max ? ?) in match (if leb zu1 zu2 then zu2 else zu1 );
        change with (max ? ?) in match (if leb (max zu1 zu2) zv2 then zv2 else max zu1 zu2);
        change with (leb (S ?) ?) in match (match fresh_var_v vv in nat return λ_:ℕ.bool with 
                [O⇒false|S (q:ℕ)⇒leb (s+n+m) q]);
        change with (max ? ?) in match (if leb ? ? then ?  else ?);
        change with (max ? ?) in match (if leb (S (s+n+m)) (fresh_var_v vv) then fresh_var_v vv else S (s+n+m));
        change with (max ? ?) in match (if leb (max (S (s+n+m)) (fresh_var_v vv))
          (fresh_var_e (push e [ν(s+n+m)←b])) 
     then fresh_var_e (push e [ν(s+n+m)←b]) 
     else max (S (s+n+m)) (fresh_var_v vv));
        change with (max ? ?) in match (if leb (fresh_var_b b) (fresh_var_e e) 
      then fresh_var_e e 
      else fresh_var_b b);
        #Hv2 #Hu1u2 #Hmax lapply (le_maxl … Hmax) lapply (le_maxr … Hmax)
        #Hmax1 #Hmax2 lapply (Hu1u2 Hmax2) -Hu1u2 * #Hu1u21 #Hu1u22
        cut (zv2 ≤ s+n) /2/ -Hmax #Hmax lapply (Hv2 Hmax)
        -Hv2 * #Hv21 #Hv22 %
        [ >Hv21 normalize
        | @(to_max …) [@(to_max …) /2/ | normalize lapply Hu1u22
          @(Environment_simple_ind2 … e)
          [ normalize change with (leb (S ?) ?) in match (match fresh_var_b b in nat return λ_:ℕ.bool with 
              [O⇒false|S (q:ℕ)⇒leb (s+n+m) q]);
            change with (max ? ?) in match(if ? then ? else ?);
            change with (max ? ?) in match (if leb (S (s+n+m)) (fresh_var_b b) then fresh_var_b b else S (s+n+m));
            #HI @(to_max ? ?) // lapply (le_maxl … HI) /2/
          | #e' #s' #HI #H1 lapply (le_maxl … H1) #H2 lapply (le_maxr … H1) -H1 #H1
            lapply (le_maxl … Hu1u22) #H3 lapply (le_maxr … Hu1u22) #H4 -Hu1u22
            normalize normalize in H1; change with (max ? ?) in match (if ? then ? else ?) in H1;
            lapply (le_maxl … H1) #H5 lapply (le_maxr … H1) -H1 #H1
            cut (max (fresh_var_b b) (fresh_var_e e')≤n+s)
            [ @(to_max …) //
            | #H6 lapply (HI H6) -HI #HI cases (leb (fresh_var_e (push e' [ν(s+n+m)←b])) (fresh_var_s s'))
              normalize /2/
            ]
          ]

            ]
        ]
      >(aux_read_back1 (val_to_term (pvar ν(s+n+m))) (val_to_term v2) (push e [ν(s+n+m)←b]))
      >(push_lemma …)
      change with (psubst ? (read_back_b ?)) in match (match [ν(s+n+m)←b] return λ_:Substitution.pifSubst with 
        [subst (x:Variable)   (b0:Byte)⇒psubst x (read_back_b b0)]);
      >(atomic_subst …) >Hu1u21 >(push_lemma …)
      change with (psubst ? (read_back_b ?)) in match (match [ν(s+n+m)←b] return λ_:Substitution.pifSubst with 
        [subst (x:Variable)   (b0:Byte)⇒psubst x (read_back_b b0)]); >(aux_read_back3 … ((m+s+n))) (*? controllare S?*)
        [ @eq_f lapply (le_maxl … Hv22) -Hv22 #Hv22 lapply Hv22 <Hv21 >zv2_def in Hmax1;
          change with (fresh_var_tv ?) in match (pi1 nat ? ?); >Hv21 #Hfvv2
          cut (fresh_var_t (val_to_term v2) ≤ s)
          [ <(fresh_var_val_to_term) assumption]
          -Hfvv2#Hfvv2 #_ @pif_subst_lemma /2/
        | normalize
        | normalize lapply (le_maxr … Hu1u22) #He normalize in He;
          (*anche questa conclusione sulla fresh_var è difficilmente dimostrabile
            con la definizione della pif_subst usata sinora*)
          change with (fresh_var_t (val_to_term v2)) in match (fresh_var_tv_Sig … );
          #x #Hx lapply (fresh_dom_e … Hx) -Hx #Hx
      ]
    | #u1 #u2 #H1 #H2 #s #Hs lapply (H1 s) cases (underline_pifTerm t1 s) #c #n
      cases c #b #e lapply (H2 (s+n)) normalize @sigma_prop_gen #zu1 #zu1_def #zu1_prop
      @sigma_prop_gen #zu2 #zu2_def #zu2_prop @sigma_prop_gen #zt1 #zt1_def #zt1_prop