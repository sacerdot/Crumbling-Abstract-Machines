include "variables.ma".

definition closed_t≝  λt. ∀x. fvb_t x t = false.
definition closed_c≝  λc. ∀x. fvb x c = false.
definition closed_tv≝ λv. ∀x. fvb_tv x v = false.
definition closed_v≝ λv. ∀x. fvb_v x v = false.

lemma closed_abstr_appl_to_l:
 ∀x, t1, t2. closed_tv (abstr x (appl t1 t2))→ closed_tv (abstr x t1).

#x #t1 #t2 normalize #H #y lapply (H y) cases veqb normalize // #H'
lapply (gtb_O … H') -H' #H' cut (free_occ_t y t1 = 0) // #H1 >H1 //
qed.

lemma closed_abstr_appl_to_r:
 ∀x, t1, t2. closed_tv (abstr x (appl t1 t2))→ closed_tv (abstr x t2).
#x #t1 #t2 normalize #H #y lapply (H y) cases veqb normalize // #H'
lapply (gtb_O … H') -H' #H' cut (free_occ_t y t2 = 0) /2/ qed.

lemma closed2: 
 (∀t, x. closed_tv (abstr x t) → 
  (closed_t t ∨ (fvb_t x t = true  ∧ ∀y. fvb_t y t = true → y = x))) ∧
 (∀v, x. closed_tv (abstr x (val_to_term v)) →
  (closed_tv v ∨ (fvb_tv x v = true  ∧ ∀y. fvb_tv y v = true → y = x))).
 
@pifValueTerm_ind
[ #v #HI #x #H lapply (HI x H) normalize //
| #t1 #t2 #H1 #H2 #x #H normalize in H;
  lapply (closed_abstr_appl_to_l … H) #H1'
  lapply (closed_abstr_appl_to_r … H) #H2'
  lapply (H1 … H1') -H1 #H1
  lapply (H2 … H2') -H2 #H2
  elim H1 elim H2
  [ -H1 -H2 #H1 #H2 @or_introl //
  | -H1 -H2 * #H1a #H1b #H2 @or_intror % /2/
    #y whd in match (fvb_t ? ?); lapply (H1b y)
    whd in match (fvb_t ? ?);
    whd in match (free_occ_t ? (appl ? ?));
    -H1b #H1b #H @H1b lapply (gtb_O_true … H)
    #He elim He #e -He lapply (H2 y)
    whd in match (fvb_t y t1);
    -H2 #H2 lapply (gtb_O … H2) -H2 #H2 >H2 normalize
    #He >He normalize //
  | -H1 -H2 #H1 * #H2a #H2b @or_intror % /2/
  | -H1 -H2 * #H2a #H2b * #H1a #H1b @or_intror % /2/
    #y lapply (H1b y) lapply (H2b y)
    whd in match (fvb_t ? t1);
    whd in match (fvb_t ? t2);
    whd in match (fvb_t ? (appl ? ?));
    whd in match (free_occ_t ? (appl ? ?));
    cases free_occ_t cases free_occ_t normalize
    [ #_ #_ #abs destruct
    | #n #_ #H @H
    | #n #H #_ @H
    | #n #m #_ #H @H
    ]
  ]
| #y #x #H @or_intror %
  [ lapply (H y) normalize >veqb_simm >veqb_true >if_t cases veqb normalize //]
  #z normalize cut (veqb z y = true ∨ veqb z y = false) // *
  #Hzy >Hzy normalize [2: #abs destruct] #_
  lapply (H z) normalize lapply (veqb_true_to_eq z y) * #Heq #_
  lapply (Heq Hzy) -Heq #Heq destruct >veqb_true >if_t
  cut (veqb y x = true ∨ veqb y x = false) // * #Hyx >Hyx normalize
  [ 2: #abs destruct ] #_
  lapply (veqb_true_to_eq y x) * #Heq #_ @(Heq Hyx)
| #t #y #HI #z #H
  cut (veqb z y = true ∨ veqb z y = false) // * #Hzy
  [ normalize >Hzy @or_introl #x
    cut (veqb x y = true ∨ veqb x y = false) // * #Hxy >Hxy // >if_f
    normalize in H; lapply (veqb_true_to_eq z y) * #Heq #_ lapply (Heq Hzy)
    -Heq #Heq destruct lapply (H x) >Hxy >if_f >if_f //
  | whd in match (fvb_tv ? (abstr y t));
    cut (free_occ_v z (abstr y t) =0 ∨ ∃n. free_occ_v z (abstr y t)= S n)
    [ cases free_occ_v [ /2/ | #m @or_intror /2/] ] * #Hw
    [ >Hw normalize @or_introl #x 
      cut (veqb x y = true ∨ veqb x y = false) //  * #Hxy >Hxy normalize //
      (*bisogna dire che \y.t è chiuso siccome \z.\y.t è chiuso e z non occorre in \y.t
        fatto ciò, sappiamo che t è chiuso, da cui la conclusione è triviale o che tutte 
        le varabili che appaiono in t sono uguali a y, dunque la tesi è vera poichè se
        fosse falsa si avrebbe y = x in assurdo con Hxy*)
      lapply (H x) normalize >Hxy >if_f
      cut (veqb x z = true ∨ veqb x z = false) // * #Hxz >Hxz normalize //
      #_ lapply (veqb_true_to_eq x z) * #Heq #_ lapply (Heq Hxz) -Heq #Heq
      destruct normalize in Hw; >Hxy in Hw; >if_f #Hfo >Hfo normalize //
    | elim Hw #m -Hw #Hw >Hw whd in match (gtb ? ?);
      (* or_intror perché sappiamo che z appare in (abstr y t), dunque il ramo sinistro è sicuramente false *)
      @or_intror % // #x cut (veqb x z = true ∨ veqb x z = false) // * #Hxz
      [ lapply (veqb_true_to_eq x z) * #Heq #_ lapply (Heq Hxz) -Heq #Heq
        destruct #_ //
      | lapply (H x) normalize >Hxz >if_f  #H1 #H2 @False_ind
        lapply H1 >H2 #abs destruct
      ]
    ]
  ]
] qed.

corollary closed_abstr: 
 ∀t, x. closed_tv (abstr x t) → 
  (closed_t t ∨ (fvb_t x t = true  ∧ ∀y. fvb_t y t = true → y = x)).
lapply closed2 * #H #_ @H qed.

lemma closed_distr: ∀t1, t2. closed_t (appl t1 t2) → closed_t t1 ∧ closed_t t2.
#t1 #t2 normalize #H % #x lapply (gtb_O … (H x)) /2/ cases free_occ_t normalize
[ 1: #H >H // | #n #abs destruct] qed.

(*
lemma closed0: 
 (∀t. ¬(closed_t t ∧ ¬(closed_t t))) ∧
  ∀v. ¬(closed_tv v ∧ ¬(closed_tv v)).

%
[ #t % * #H1 #H2 @(absurd … (closed_t t)) [ @H1 | @H2 ]
| #v % * #H1 #H2 @(absurd … (closed_tv v)) [ @H1 | @H2 ] 
qed.

lemma closed1: 
 (∀t. (closed_t t ∨ ¬(closed_t t))) ∧
  ∀v. (closed_tv v ∨ ¬(closed_tv v)).
  
@pifValueTerm_ind
[ #v normalize //
| #t1 #t2 normalize #H1 #H2 elim H1 elim H2
  [ #H1' #H2' @or_introl #x lapply (H1' x) lapply (H2' x)
    -H1' -H2' #H1' #H2' >(gtb_O … H1') >(gtb_O … H2') //
  | #H1' #H2' @or_intror % #H elim H1' #H1' @H1'
    #h lapply(gtb_O … (H h)) cases (free_occ_t h t2) 
    normalize // #n #abs <(plus_n_Sm (free_occ_t h t1) n) in abs;
    #abs destruct
  | #H1' #H2' @or_intror % #H elim H2' #h2'' @h2'' #x lapply (H x)
    cases free_occ_t cases free_occ_t /2/ #n #m normalize //
  | #H1' #H2' @or_intror % #H elim H2' #h2'' @h2'' #x lapply (H x)
    cases free_occ_t cases free_occ_t /2/ #n #m normalize //
  ]
| #y normalize @or_intror % #H @(absurd … (gtb (if veqb y y then 1 else 0) 0 = false))
  // >veqb_true normalize //
| #t #x #H elim H #H'
  [ @or_introl normalize #z normalize in H'; cases veqb normalize //
  | normalize normalize in H';
    cut (((∀x0:Variable.gtb (if veqb x0 x then O else free_occ_t x0 t ) O=false
         ∨(¬gtb (if veqb x0 x then O else free_occ_t x0 t ) O=false))))
    [ // #x0 elim H' #H'' 
      cut (veqb x0 x = true ∨ veqb x0 x = false) //
    ]
    #H
*)