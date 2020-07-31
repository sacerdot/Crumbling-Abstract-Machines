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

include "alternative_pif_subst.ma".

lemma irrelevant:
 (∀t,n,n',y,t',H,H'. pi1 … (pif_subst_sig (S n) y t' t H) = pi1 … (pif_subst_sig (S n') y t' t H')) ∧
 (∀v,n,n',y,t',H,H'. pi1 … (pif_subst_sig (S n) y t' (val_to_term v) H) = pi1 … (pif_subst_sig (S n') y t' (val_to_term v) H')).

@pifValueTerm_ind
[ #v #H @H
| #t1 #t1 #H1 #H2 #n #n' #y #t'
| #x #n #n' #y #t' #H #H' @eq_f
  cut (∀HHT',HHF'.
     (pif_subst_sig (S n) y t' (val_to_term (pvar x)) H
  = match veqb y x
    return λb. veqb y x = b → t_size (val_to_term (pvar x)) ≤ S n' →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb y x = true.
        λp: t_size (val_to_term (pvar x))≤ S n'.
         «t', HHT' H p»
     | false ⇒ λH: veqb y x = false.
        λp: t_size (val_to_term (pvar x)) ≤ S n'.
         «val_to_term (pvar x), HHF' H p»
     ] (refl bool (veqb y x)) H')
     )
  [2: #UU @UU] #HHT' #HHF'
  cut (∀HHT, HHF. eq (Σu:pifTerm
  .t_size u
   =t_size (val_to_term (pvar x))
    +free_occ_t y (val_to_term (pvar x))*(t_size t'-1)
   ∧(∀z:Variable
     .free_occ_t z u
      =if veqb y z 
       then free_occ_t z (val_to_term (pvar x))*free_occ_t z t' 
       else free_occ_t y (val_to_term (pvar x))*free_occ_t z t'
                +free_occ_t z (val_to_term (pvar x)) ))

(match veqb y x
    return λb. veqb y x = b → t_size (val_to_term (pvar x)) ≤ S n →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb y x = true.
        λp: t_size (val_to_term (pvar x))≤ S n.
         «t', HHT H p»
     | false ⇒ λH: veqb y x = false.
        λp: t_size (val_to_term (pvar x)) ≤ S n.
         «val_to_term (pvar x), HHF H p»
     ] (refl bool (veqb y x)) H)

(match veqb y x
    return λb. veqb y x = b → t_size (val_to_term (pvar x)) ≤ S n' →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb y x = true.
        λp: t_size (val_to_term (pvar x))≤ S n'.
         «t', ?»
     | false ⇒ λH: veqb y x = false.
        λp: t_size (val_to_term (pvar x)) ≤ S n'.
         «val_to_term (pvar x), ?»
     ] (refl bool (veqb y x)) H')
                
                )
[4: #UU @UU
| skip
| skip
| #HHT #HHF cases veqb in HHT HHT' HHF HHF' ⊢ %; normalize /2/
]
| #t1 * #x #HI #n #n'* #y #t' #H #H' @eq_f
  whd in match  (pif_subst_sig (S n) (νy) t' (val_to_term (abstr (νx) t1)) H);
  
(*  whd in match (pif_subst_sig (S n') y t' (val_to_term (abstr x t)) H'); *)
  cut (∀K, K1, K2, K3. eq 
  
  (Σu:pifTerm
  .t_size u
   =t_size (val_to_term (abstr (νx) t1))
    +free_occ_t (νy) (val_to_term (abstr (νx) t1))*(t_size t'-1)
   ∧(∀z:Variable
     .free_occ_t z u
      =if veqb (νy) z 
       then free_occ_t z (val_to_term (abstr (νx) t1))*free_occ_t z t' 
       else free_occ_t (νy) (val_to_term (abstr (νx) t1))*free_occ_t z t'
                +free_occ_t z (val_to_term (abstr (νx) t1)) ))
                
  (pif_subst_sig (S n) (νy) t' (val_to_term (abstr (νx) t1)) H)
  
  (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S n' → Σu: pifTerm. ?
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), K … H p»
        | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S n' → Σu: pifTerm. ?
         with
          [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S n' → Σu: pifTerm. ? 
            with
            [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig (t_size t1) (νx) (val_to_term (pvar ν(z))) t1 (le_n (t_size t1))) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size t1) (νy) t' a ?)))), K1 … H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), K2 … H HH Hfv p»
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig (t_size t1) (νy) t' t1 (le_n (t_size t1)))))), K3 …  H HH p»
          ] (refl …)
        ]  (refl bool (veqb (νy) (νx))) H') )
(*(subst_aux_5 … t1 (νx) z a n h p)*)

     [3: #UU @UU [2: #H1 #H2 #H3 @(subst_aux_8 (νy) t' n' (νx) t1 H1 H2 H3) /2/ 