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
include "utils.ma".
include "libnat.ma".

let rec Environment_double_ind2 (P: Environment → Environment → Prop)
(H1: P Epsilon Epsilon)
(H3: ∀e, s. P (Cons e s) Epsilon)
(H4: ∀e, s. P Epsilon (Cons e s))
(H2: ∀e.∀f.∀s.∀t. P e f → P (Cons e s) (Cons f t))
e f on e ≝
 match e return λe. P e f with
 [ Epsilon ⇒ match f with 
   [ Epsilon ⇒ H1
   | Cons f t ⇒ H4 f t
   ]
 | Cons e s ⇒ match f with 
   [ Epsilon ⇒ H3 e s
   | Cons f t ⇒ H2 e f s t (Environment_double_ind2 P H1 H3 H4 H2 e f)
   ]
 ].


let rec e_len e on e ≝
 match e with
 [ Epsilon ⇒ 0
 | Cons e s ⇒ S (e_len e)
 ]
.

lemma len_lemma: ∀e, f. e_len e ≠ e_len f → e ≠ f.
@Environment_double_ind2
[ normalize #H cut (0=0) [ @refl ] #H1 % #_ elim H
  #H' @H' @refl
| #e #s normalize #_ % #H destruct
| #e #s normalize #_ % #H destruct
| #e #f #s #t #HI normalize
  #H elim H #HH cut (e_len e = e_len f → False)
  [ #HHH @HH @eq_f @HHH ] #HHH
  cut (e ≠ f)
  [ @HI % @HHH ] #H4 % elim H4 -H4 #H4 #H5 @H4
  destruct //
] qed.

lemma push_len: ∀e, s. e_len (push e s) = S (e_len e).
@Environment_simple_ind2
[ #s normalize //
| #e #s #H #s1 normalize >H //
] qed.

lemma concat_len: ∀f,e. e_len (concat e f) = (e_len e + e_len f).
@Environment_simple_ind2
[ #e normalize //
| #e #s #HI #t normalize >HI //
] qed.

lemma concat_to_push :∀e, s. concat (Cons Epsilon s) e = push e s.
@Environment_simple_ind2
[ #s normalize //
| #e #s #HI #t normalize >HI //
] qed.

lemma env_lemma1:
 ∀ h, f, e, s, u. concat (push e s) f=push h u → 
  s=u ∧ h = concat e f.
@Environment_double_ind2
[ #e #s #u normalize cases e
  [ normalize #H destruct % @refl
  | #e #y normalize cases e normalize [ #H destruct ]
    #ee #ss normalize #H destruct
  ]
| #h #hs #e #s #u normalize generalize in match hs;
  @(Environment_double_ind2 … e h)
  [ #hs normalize #H destruct
  | #ee #ss #hs normalize cases ee
    [ normalize #HH destruct % //
    | #e3 #s3 normalize cases e3
      [ #H normalize destruct
      | #e4 #s4 normalize #H destruct
      ]
    ]
  | #e1 #s1 #hs normalize cases e1
    [ normalize #H destruct % @refl
    | #e2 #s2 normalize cases e2
      [ #H destruct
      | #e3 #s3 #H destruct
      ]
    ]
  | #e1 #e2 #s1 #s2 normalize #HI #hs #H
  cut (push e1 s = Cons (push e2 u) s2)
  [ destruct @e0 ] #e0
    lapply (HI … e0) * #Ha #Hb % // @eq_f2 //
    lapply H -H cases (push e1 s)
    [ #H destruct
    | #e3 #s3 #H destruct @refl
    ]
  ]
| #f #sf #e #s #u normalize cases e
  [ cases f
    [ normalize #H destruct
    | #ff #sff normalize #H destruct
    ]
  | #e1 #s2 normalize cases f
    [ normalize #H destruct
    | #ff #sff normalize #H destruct
    ]
  ]
| #h #f #sh #sf #HI #e #s #u normalize #H
  cut (concat (push e s) f = push h u) [ destruct @e0 ]
  #HH lapply (HI … HH) * #Ha #Hb % // >Hb @eq_f2 //
  lapply H generalize in match (concat (push e s) f);
  generalize in match (push h u);
  #j #k #Hf destruct //
] qed.

lemma env_lemma2: ∀f, e, s. concat (Cons e s) f = concat e (push f s).
@Environment_simple_ind2
[ normalize //
| #f #s #HI #e #s1 normalize >HI @refl
] qed.

lemma env_lemma3: ∀f, e, s, t, u.
 (push (Cons e u) s=Cons f t) →
  ∃d. f = push d s ∧ Cons e u = Cons d t.
@Environment_simple_ind2
[ #e #s #t #u normalize cases e
  [ normalize #H destruct
  | #ee #ss normalize #H destruct
  ]
| #f #sf #HI #e #s #t #u normalize #H
  cut (t=u)
  [ lapply H generalize in match (push e s); #j #HH destruct @refl ] #H1
  >H1 cut (push e s = Cons f sf)
  [ destruct @e0 ] cases e
  [ normalize #HH destruct % [ @Epsilon ] % //
  | #j #k #e0 lapply (HI … e0) * #x * #Ha #Hb >Ha >Hb % [ @(Cons x sf) ]
    normalize % //
  ]
] qed.

lemma env_lemma4: ∀f, e, s. push (concat e f) s = concat (push e s) f.
@Environment_simple_ind2
[ #e #s normalize @refl
| #f #sf #H #e #s normalize >H @refl
] qed.

lemma env_lemma5: ∀f, e, s. concat (Cons e s) f = concat e (push f s).
@Environment_simple_ind2
[ #e #s normalize //
| #ff #sf #HI #e #s normalize >HI //
] qed.

lemma e_len_lemma: ∀e, f. e = f → e_len e = e_len f. // qed.

lemma concat_decomposition1: ∀f, h, g, e.
 concat e f = concat g h →
  (∃d. e = concat g d  ∧ h = concat d f) ∨
   ∃d. g = concat e d ∧  f = concat d h.
@Environment_double_ind2
[ #g #e normalize #H destruct @or_introl % [ @Epsilon] % //
| #f #s #g #e normalize #H @or_intror % [ @(Cons f s) ] % // <H normalize //
| #h #s #g #e normalize #H @or_introl % [ @(Cons h s) ] % // >H normalize //
| #f #h #sf #sh normalize #HI #g #e #H cut (concat e f = concat g h)
  [ destruct @e0
  | #HH lapply (HI … HH) cut (sf = sh)
    [ lapply H generalize in match (concat e f); #j
      generalize in match (concat g h); #k #HHH destruct @refl ]
    #HHH >HHH -HHH -HI * * #x * #Ha #Hb >Ha >Hb
    [ @or_introl % [ @x ]
    | @or_intror % [ @x ]
    ] % //
  ]
] qed.

lemma abs_cons: ∀e, s. e = Cons e s → False.
@Environment_simple_ind2
[ #s #abs destruct
| #e #s #HI #t normalize #H @(HI … s) destruct @e0
] qed.

lemma abs_concat: ∀e, f, s. e = concat (Cons e s) f → False.
#e #f #s /2/ qed.
lemma abs_concat2: ∀e, f, s, t. e = Cons (concat (Cons e s) f) t → False.
#e #f #s #t /2/ qed.

lemma cons_concat: ∀f, e, s, g.
 Cons e s = concat g f → 
  g = Cons e s ∧ f= Epsilon ∨ (∃d. e = concat g d ∧ f = Cons d s).
@Environment_simple_ind2
[ normalize #e #s #g #H % >H % @refl
| #f #sf #HI #e #s #g normalize cases e
  [ normalize cases g cases f
    [ normalize #H destruct @or_intror % [ @Epsilon ] % @refl
    | #gg #ll normalize #abs destruct
    | #jj #kk normalize #abs destruct
    | #e1 #jk #e2 #kl normalize #abs destruct
    ]
  | #ee #ss #HH cut (Cons ee ss = concat g f)
    [ destruct @e0 ] #HHH lapply (HI … HHH) *
    [ * #Hf #Hf2 >Hf in HHH; lapply HH cases f
      [ normalize #HHf #HHH  destruct @or_intror % [ @Epsilon ] % //
      | #ff #sf normalize cases ff
        [ normalize #_ #abs destruct @False_ind @(abs_cons … e0)
        | #fff #ffs normalize #_ #gh destruct @False_ind @(abs_concat2 … e0)
        ]
      ]
    | * #x * #H1 #H2 @or_intror destruct % [ @(Cons x ss) ] normalize % //
    ]
  ]
] qed.

lemma cons_push_decomposition: ∀e, f, s, t.
 Cons e s = push f t →
  (s=t ∧ f= Epsilon ∧ e=Epsilon) ∨ ∃d. e = push d t ∧ f = Cons d s.
@Environment_double_ind2
[ #s #t normalize #H destruct % % // % //
| #e #s #t #u normalize #abs destruct
| #f #s #t #u normalize #H destruct @False_ind lapply e0
  cases f [ normalize #abs destruct | #hh #jj normalize #abs destruct ]
| #e #f #s #t #HI #u #v normalize #H cut (Cons e s = push f v)
  [ destruct @e0 ] #HH cut (t=u)
  [ lapply H
    generalize in match (Cons e s);
    generalize in match (push f v); #y #r #HHH destruct @refl ]
   #Hc lapply (HI … HH) >Hc *
   [  * * #Ha #Hb #Hd destruct @or_intror % [ @Epsilon ] normalize % //
   | * #x * #Ha #Hb @or_intror % [@(Cons x s)] normalize % //
   ]
] qed.

lemma push_eq_inv: ∀e, f, s, t. push e s = push f t → e = f ∧ s=t.
@Environment_double_ind2
[ #s #t normalize #abs destruct % @refl
| 2,3: #e #s #t #u normalize cases e
  [ 1,3: normalize #H destruct
  | 2,4: #ee #ss normalize #abs destruct
  ]
| #e #f #se #sf #HI #t #u normalize #H
  cut (push e t = push f u)
  [ destruct @e0 ] #e0 lapply (HI … e0) * #Ha #Hb >Ha >Hb
  cut (se = sf)
  [ lapply H generalize in match (push e t); #k
    generalize in match (push f u); #j #H destruct @refl ]
  #sesf >sesf % @refl
] qed.
