Require Export Cring.
Require Export Integral_domain.

(* Real numbers *)
Require Import Reals.
Require Import RealField.

Lemma Rsth : Setoid_Theory R (@eq R).
constructor;red;intros;subst;trivial.
Qed.

Global Instance Rops: (@Ring_ops R 0%R 1%R Rplus Rmult Rminus Ropp (@eq R)).

Global Instance Rri : (Ring (Ro:=Rops)).
constructor;
try (try apply Rsth;
   try (unfold respectful, Proper; unfold equality; unfold eq_notation in *;
  intros; try rewrite H; try rewrite H0; reflexivity)).
 exact Rplus_0_l. exact Rplus_comm. symmetry. apply Rplus_assoc.
 exact Rmult_1_l.  exact Rmult_1_r. symmetry. apply Rmult_assoc.
 exact Rmult_plus_distr_r. intros; apply Rmult_plus_distr_l. 
exact Rplus_opp_r.
Defined.

Global Instance Rcri: (Cring (Rr:=Rri)).
red. exact Rmult_comm. Defined.

Lemma R_one_zero: 1%R <> 0%R.
discrR.
Qed.

Global Instance Rdi : (Integral_domain (Rcr:=Rcri)). 
constructor. 
exact Rmult_integral. exact R_one_zero. Defined.
