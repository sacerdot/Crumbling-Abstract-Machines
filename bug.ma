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

include "alpha.ma".

lemma rhs_beta_concat_distro2: ∀f, e, x, l. (rhs (beta_e e (l+e_len f)) x ∨ rhs  (beta_e f (l)) x) →  rhs (beta_e (concat e f) l) x.
@Environment_simple_ind2
[ #e #x #l normalize * // #H @False_ind @H 
| #f * #y #b #HI #e #x #l normalize *
  [ #HH @or_intror @HI @or_introl //
  | * #HH 
    [ @or_introl @HH
    | @or_intror @HI @or_intror @HH
    ]
  ]
] qed.

lemma in_gamma_e: ∀l, e, x, H. 
 (inb_e x e) = false →
  (¬rhs l x ) →   
   inb_e x (pi1 … (gamma_e e l H)) = false.
@list_ind
[ #e #x #H normalize #H1 #_ @H1
| * #y #y' #tl #HI #e #x #H #H1 #H2
  whd in match (gamma_e ? ? ?);
  lapply alpha_fin1 * * * * #_ #_ #He #_ #_ >He [ @refl]
  [ 2: @HI // % #Hk elim (H2) #H2 @H2 normalize @or_intror @Hk
  | elim H2 normalize >veqb_comm cases veqb // #HH @False_ind @HH @or_introl //
  ]
] qed. 

lemma gamma_concat_irrelevance: ∀f, e, l, t, H.
 (∀x. domb_e x f = true → inb_e x e = false ∧ inb_e x t = false) →
  fresh_var_e (concat e f) ≤ l →
  pi1 … (gamma_e t (beta_e (concat e f) l) H) = pi1 … (gamma_e t (beta_e e (l+e_len f)) ?). 
[ 2: % // #k #Hk elim H #H' #_ @H' @rhs_beta_concat_distro2 @or_introl @Hk ]
@Environment_simple_ind2
[ #e #l #t whd in match (concat ? ?); whd in match (e_len ?); #H
  generalize in match ( conj ? ? ? ?);
  generalize in match H; cut (l+0=l) // #HH >HH //
| #f * * #y #b #HI #e #l #t
  whd in match (concat ? ?);
  whd in match (beta_e ? ?); #H
  whd in match (gamma_e ? ? ?); #HH #H2
  generalize in match (gamma_e_aux3 ? ? ? ? ? ?);
  generalize in match (gamma_e_aux2 ? ? ? ?);
  generalize in match (conj ? 
   (distinct_rhs (beta_e e (l+e_len (Cons f [νy←b])))) ? ?); 
  generalize in match H;
   whd in match (e_len (Cons ? ?)); <plus_n_Sm
  #P1 #P2 #P3 >HI
  [ 2: @(le_S … (le_maxl … H2)) 
  | 3: #k #Hk @HH normalize >Hk >if_monotone @refl] #P4
   lapply ssc_in * * * * #_ #_ #He #_ #_ >He [ // ]
   >in_gamma_e
   [ @refl
   | 3: elim (HH (νy) ?) // normalize >neqb_refl //
   | % #Hy elim (betae_rhs_bound … Hy) #Ha #_ @False_ind
     lapply (transitive_le … (le_S … Ha) (le_maxl … (le_maxr … H2))) /2/
   ]
] qed.

lemma in_gamma_b: ∀l, e, x, H. 
 (inb_b x e) = false →
  (¬rhs l x ) →   
   inb_b x (pi1 … (gamma_b e l H)) = false.
@list_ind
[ #e #x #H normalize #H1 #_ @H1
| * #y #y' #tl #HI #e #x #H #H1 #H2
  whd in match (gamma_e ? ? ?);
  lapply alpha_fin1 * * * * #_ #He #_ #_ #_ >He [ @refl]
  [ 2: @HI // % #Hk elim (H2) #H2 @H2 normalize @or_intror @Hk
  | elim H2 normalize >veqb_comm cases veqb // #HH @False_ind @HH @or_introl //
  ]
] qed. 


lemma gammab_concat_irrelevance: ∀f, e, l, t, H.
 (∀x. domb_e x f = true → inb_e x e = false ∧ inb_b x t = false) →
  fresh_var_e (concat e f) ≤ l →
  pi1 … (gamma_b t (beta_e (concat e f) l) H) = pi1 … (gamma_b t (beta_e e (l+e_len f)) ?). 
[ 2: % // #k #Hk elim H #H' #_ @H' @rhs_beta_concat_distro2 @or_introl @Hk ]
@Environment_simple_ind2
[ #e #l #t whd in match (concat ? ?); whd in match (e_len ?); #H
  generalize in match ( conj ? ? ? ?);
  generalize in match H; cut (l+0=l) // #HH >HH //
| #f * * #y #b #HI #e #l #t
  whd in match (concat ? ?);
  whd in match (beta_e ? ?); #H
  whd in match (gamma_b ? ? ?); #HH #H2
  generalize in match (gamma_b_aux3 ? ? ? ? ? ?);
  generalize in match (gamma_b_aux2 ? ? ? ?);
  generalize in match (conj ? 
   (distinct_rhs (beta_e e (l+e_len (Cons f [νy←b])))) ? ?); 
  generalize in match H;
   whd in match (e_len (Cons ? ?)); <plus_n_Sm
  #P1 #P2 #P3 >HI
  [ 2: @(le_S … (le_maxl … H2)) 
  | 3: #k #Hk @HH normalize >Hk >if_monotone @refl] #P4
   lapply ssc_in * * * * #_ #Hb #_ #_ #_ >Hb [ // ]
   >in_gamma_b
   [ @refl
   | 3: elim (HH (νy) ?) // normalize >neqb_refl //
   | % #Hy elim (betae_rhs_bound … Hy) #Ha #_ @False_ind
     lapply (transitive_le … (le_S … Ha) (le_maxl … (le_maxr … H2))) /2/
   ]
] qed.