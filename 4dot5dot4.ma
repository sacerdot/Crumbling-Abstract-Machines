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

include "underline_readback.ma".

let rec subt t1 t2 on t2 ≝ 
 match t2 with
 [ val_to_term v ⇒ subt_v t1 v
 | appl u1 u2 ⇒ t1 = u1 ∨ t1 = u2 ∨ subt t1 u1 ∨ subt t1 u2
 ]

and subt_v t v on v ≝ 
 match v with
 [ pvar x ⇒ False
 | abstr x t1 ⇒ t = t1 ∨ subt t t1
 ]
.
 
definition tint ≝ λt1.λt2. t1=t2 ∨ subt t1 t2.

let rec subc c d on d ≝
 match d with 
 [ CCrumble b e ⇒ subc_b c b ∨ subc_e c e]
 
and subc_b c b on b ≝
 match b with
 [ CValue v ⇒ subc_v c v
 | AppValue v w ⇒ subc_v c v ∨ subc_v c w 
 ]
 
and subc_v c v on v ≝ 
 match v with
 [ var x ⇒ False
 | lambda x d ⇒ c = d ∨ subc c d
 ]
 
and subc_e c e on e ≝
 match e with
 [ Epsilon ⇒ False
 | Snoc e s ⇒ subc_s c s ∨ subc_e c e
 ]
 
and subc_s c s on s ≝ 
 match s with
 [ subst x b ⇒ subc_b c b ]
 .   

definition cinc ≝ λc.λd. c=d ∨ subc c d.

lemma izilemma:∀e, c, x, b. (subc_e c (push e [x←b])) → (subc_b c b ∨ subc_e c e).
@Environment_simple_ind2
[ //
| #e #s #HI #c #x #b whd in match (push ? ?); whd in match (subc_e ? ?); *
  [ #H normalize @or_intror @or_introl @H
  | #H lapply (HI … H) normalize *
    [ /2/ | /3/]
  ]
] qed.

lemma izilemma1: ∀f, e, c. subc_e c (concat e f) → subc_e c e ∨ subc_e c f.
@Environment_simple_ind2
[ /2/
| #f #sf #HI #e #c whd in match (concat ? ?);
  whd in match (subc_e ? ?); * /3/
  #H lapply (HI … H) normalize * /3/
] qed. 
    
lemma term:
(∀t, s, c. subc c (fst … (underline_pTerm t s)) →
   ∃u, n. (c = fst … (underline_pTerm u n)) ∧ (tint u t)) ∧
(∀v, s, c. subc_v c (fst … (overline v s)) →
   ∃u, n. (c = fst … (underline_pTerm u n)) ∧ (subt_v u v)).
@pValueTerm_ind
[ #v #HI #s #c whd in match (underline_pTerm ? ?); lapply (HI s c) cases overline
 #a #b -HI #HI normalize *
 [ #H lapply (HI H) * #k * #n * #Ha #Hb % [ @k] % [@n] % // @or_intror //]
 #abs @False_ind @abs
| 3: #x #s #c normalize #abs @False_ind @abs
| 4: #t #x #HI #s #c normalize lapply (HI s c) 
  cut ((c = (\fst (underline_pTerm t s)) ∨ subc c (\fst (underline_pTerm t s))) = (subc_v c (\fst  (let 〈c0,n〉 ≝underline_pTerm t s in 〈𝛌x.c0,n〉))))
  [ cases underline_pTerm #a #b normalize //] #Haux <Haux -Haux -HI
  #HI * #H  [ 2: @HI@H ] % [@t] % [@s] % // @or_introl //
| #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s lapply (H1 s) cases (overline v1 s) #vv #n
      normalize lapply (H2 n) cases (overline v2 n) #ww #m normalize
      #H2 #H1 #c * [ 2: #abs @False_ind @abs ]
      *
      [ #H elim(H1 c (or_introl … H)) #k * #y * #Ha #Hb
        % [@k] % [@y] % // @or_intror lapply Hb -Hb *
        #Hb [ @or_introl @or_introl @or_introl //
            | @or_introl @or_intror //
            ]
      | #H elim(H2 c (or_introl … H)) #k * #y * #Ha #Hb
        % [@k] % [@y] % // @or_intror lapply Hb -Hb *
        #Hb [ @or_introl @or_introl @or_intror //
            | @or_intror //
            ]
      ]
    | #u1 #u2 normalize #H1 #H2 #s lapply (H1 s)
      change with (underline_pTerm (appl u1 u2) ?)
        in match ( match u2 in pTerm with [_⇒ ?]);
      cases (underline_pTerm (appl u1 u2) s) * #b #e #n normalize -H1 #H1
      lapply (H2 n) cases (overline v2 n) #ww #m normalize #H2
       #c * [ * [ #abs @False_ind @abs ]
       | #H elim(H1 c (izilemma … H)) #k * #y * #Ha #Hb
        % [@k] % [@y] % // @or_intror lapply Hb -Hb *
        #Hb [ @or_introl @or_introl @or_introl //
            | @or_introl @or_intror //
            ]
      ]
      #H elim(H2 c (or_introl … H)) #k * #y * #Ha #Hb
        % [@k] % [@y] % // @or_intror lapply Hb -Hb *
        #Hb [ @or_introl @or_introl @or_intror //
            | @or_intror //
            ]
      ]
    | #u1 #u2 #Hu1 #Hu2 #s lapply (Hu2 s) normalize
      change with (underline_pTerm (appl u1 u2) ?)
        in match ( match u2 in pTerm with [_⇒ ?]);
      cases (underline_pTerm (appl u1 u2) s) * #b1 #e1 #n -Hu2 #Hu2
      lapply Hu1 cases t1 normalize
      [ #v1 -Hu1 #Hu1 lapply (Hu1 n) cases (overline v1 n) #vv #m normalize -Hu1
        #Hu1 #c *
        [ #H elim(Hu1 c H) #k * #y * #Ha #Hb
        % [@k] % [@y] % // @or_intror lapply Hb -Hb *
        #Hb [ @or_introl @or_introl @or_introl //
            | @or_introl @or_intror //
            ]
        | >concat_epsilon_e #H elim (Hu2 c (izilemma … H) ) #k * #y * #Ha #Hb
          % [@k] % [@y] % // @or_intror lapply Hb -Hb *
          #Hb [ @or_introl @or_introl @or_intror //
              | @or_intror //
              ]
        ]
      | #r1 #r2 #H1 normalize
      lapply (H1 n) normalize
      change with (underline_pTerm (appl r1 r2) n)
        in match ( match r2 in pTerm with [_⇒ ?]);      
      cases (underline_pTerm (appl r1 r2) n ) * #b #e #m
      normalize -H1 #H1 #c * [ * #abs @False_ind @abs ]
      #H lapply (izilemma1 … H) *
      [ -H #H elim(H1 c (izilemma … H)) #k * #y * #Ha #Hb
        % [@k] % [@y] % // @or_intror lapply Hb -Hb *
        #Hb [ @or_introl @or_introl @or_introl //
            | @or_introl @or_intror //
            ]
      | -H #H lapply Hu2 normalize -Hu2 #H2
        elim (H2 c (izilemma … H)) #k * #y * #Ha #Hb
          % [@k] % [@y] % // @or_intror lapply Hb -Hb *
          #Hb [ @or_introl @or_introl @or_intror //
              | @or_intror //
              ]
      ]
    ]
  ]
] qed.
