(* -*- mode: coq; coq-prog-args: ("-allow-sprop") -*- *)

Definition iUnit : SProp := forall A : SProp, A -> A.

Definition itt : iUnit := fun A a => a.

Definition iUnit_irr (P : iUnit -> Type) (x y : iUnit) : P x -> P y
  := fun v => v.

Definition iSquash (A:Type) : SProp
  := forall P : SProp, (A -> P) -> P.
Definition isquash A : A -> iSquash A
  := fun a P f => f a.
Definition iSquash_rect A (P : iSquash A -> SProp) (H : forall x : A, P (isquash A x))
  : forall x : iSquash A, P x
  := fun x => x (P x) (H : A -> P x).

Fail Check (fun A : SProp => A : Type).

Inductive sBox (A:SProp) : Prop
  := sbox : A -> sBox A.

Definition uBox := sBox iUnit.

Definition sBox_irr A (x y : sBox A) : x = y.
Proof.
  Fail reflexivity.
  destruct x as [x], y as [y].
  reflexivity.
Defined.

Set Primitive Projections.
(* Primitive record with all fields in SProp has the eta property of SProp so must be SProp. *)
Record rBox (A:SProp) : Prop
  := rbox { runbox : A }.

(* Check that it doesn't have eta *)
Fail Check (fun (A : SProp) (x : rBox A) => eq_refl : x = @rmkbox _ (@relem _ x)).

Inductive sEmpty : SProp := .

Inductive sUnit : SProp := stt.

Inductive BIG : SProp := foo | bar.

Inductive Squash (A:Type) : SProp
  := squash : A -> Squash A.

Definition BIG_flip : BIG -> BIG.
Proof.
  intros [|]. exact bar. exact foo.
Defined.

Inductive pb : Prop := pt | pf.

Definition pb_big : pb -> BIG.
Proof.
  intros [|]. exact foo. exact bar.
Defined.

Fail Definition big_pb (b:BIG) : pb :=
  match b return pb with foo => pt | bar => pf end.

Inductive which_pb : pb -> SProp :=
| is_pt : which_pb pt
| is_pf : which_pb pf.

Fail Definition pb_which b (w:which_pb b) : bool
  := match w with
     | is_pt => true
     | is_pf => false
     end.

Inductive sNZ : nat -> SProp
  := snz : forall n, sNZ (S n).

Definition sPred (n:nat) (s:sNZ n) : nat :=
  match s with snz k => k end.

Definition spred1 n (s : sNZ (S n))
  : sPred (S n) s = sPred (S n) (snz n)
  := eq_refl.
Definition spred2 n (s : sNZ (S n))
  : sPred (S n) (snz n) = n
  := eq_refl.
Definition spred3 n (s:sNZ (S n))
  : sPred (S n) s = n
  := eq_trans (spred1 n s) (spred2 n s).

Definition sPred_S n (s:sNZ (S n))
  : sPred (S n) s = n
  := eq_refl.

Module IsPair_nosec.

  Inductive IsPair (A:Type) (B:A -> Type) : sigT B -> SProp :=
    ispair : forall x y, IsPair A B (existT B x y).

  Definition p1 A B p (i : IsPair A B p) : A :=
    match i with ispair _ _ x _ => x end.

  Definition p1_comp A B (x:A) (y:B x) (i : IsPair A B (existT B x y))
    : p1 A B _ i = x
    := eq_refl.

  (** There used to be a debruijn bug such that it reduced to [fun ... => y].
      The kernel checks after the reduction so this tests that bug is properly gone. *)
  Definition p1_lazy
    : forall A B x y (_:IsPair _ _ _), A
    := Eval lazy in fun A B (x:A) (y:B x) => p1 A B (existT B x y).

End IsPair_nosec.

Module IsPair_sec.

  Section Sec.
    Variables (A : Type) (B: A -> Type).
    Inductive IsPair : sigT B -> SProp :=
      ispair : forall x y, IsPair (existT B x y).

    Definition p1 p (i: IsPair p) : A :=
      match i with ispair x _ => x end.

    Section Comp.
      Variables (x:A) (y:B x) (i : IsPair (existT B x y)).

      Eval lazy in p1 _ i.
    End Comp.
    Definition p1_compute_insec x y (i:IsPair (existT B x y)) : p1 (existT B x y) i = x
      := eq_refl.
  End Sec.

  Definition p1_comp_nosec A B (x:A) (y:B x) (i : IsPair A B (existT B x y))
    : p1 A B _ i = x
    := eq_refl.

  Eval lazy in fun A B (x:A) (y:B x) => p1 A B (existT B x y).

End IsPair_sec.

(* Non primitive because no arguments, but maybe we should allow it for sprops? *)
Record UnitRecord : SProp := {}.

Scheme Induction for UnitRecord Sort Set.

Record sProd (A B : SProp) : SProp := sPair { sFst : A; sSnd : B }.

Scheme Induction for sProd Sort Set.

Unset Primitive Projections.
Record sProd' (A B : SProp) : SProp := sPair' { sFst' : A; sSnd' : B }.
Set Primitive Projections.

Fail Scheme Induction for sProd' Sort Set.

Record NZpack := nzpack { nzval :> nat; nzprop : sNZ nzval }.

Definition NZpack_eta (x : NZpack) (i : sNZ x) : x = nzpack x i := @eq_refl NZpack x.

(** Fixpoints on SProp values are only allowed to produce SProp results *)
Inductive sAcc (x:nat) : SProp := sAcc_in : (forall y, y < x -> sAcc y) -> sAcc x.

Definition sAcc_inv x (s:sAcc x) : forall y, y < x -> sAcc y.
Proof.
  destruct s as [H]. exact H.
Defined.

Section sFix_fail.
  Variable P : nat -> Type.
  Variable F : forall x:nat, (forall y:nat, y < x -> P y) -> P x.

  Fail Fixpoint sFix (x:nat) (a:sAcc x) {struct a} : P x :=
    F x (fun (y:nat) (h: y < x) => sFix y (sAcc_inv x a y h)).
End sFix_fail.

Section sFix.
  Variable P : nat -> SProp.
  Variable F : forall x:nat, (forall y:nat, y < x -> P y) -> P x.

  Fixpoint sFix (x:nat) (a:sAcc x) {struct a} : P x :=
    F x (fun (y:nat) (h: y < x) => sFix y (sAcc_inv x a y h)).

End sFix.


Class emptyclass : SProp := emptyinstance : forall A:SProp, A.

(** Identity! Currently we have UIP. *)
Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.

Definition transport {A} (P:A -> Type) {x y} (e:seq x y) (v:P x) : P y :=
  match e with
    srefl _ => v
  end.

Definition transport_refl {A} (P:A -> Type) {x} (e:seq x x) v
  : transport P e v = v
  := @eq_refl (P x) v.

(** We don't ALWAYS reduce (this uses a constant transport so that the
    equation is well-typed) *)
Fail Definition transport_block A B (x y:A) (e:seq x y) v
  : transport (fun _ => B) e v = v
  := @eq_refl B v.

Definition transport_refl_box (A:SProp) P (x y:A) (e:seq (sbox A x) (sbox A y)) v
  : transport P e v = v
  := eq_refl.

(** TODO add tests for binders which aren't lambda. *)
Definition transport_box :=
  Eval lazy in (fun (A:SProp) P (x y:A) (e:seq (sbox A x) (sbox A y)) v =>
                  transport P e v).

Lemma transport_box_ok : transport_box = fun A P x y e v => v.
Proof.
  unfold transport_box.
  match goal with |- ?x = ?x => reflexivity end.
Qed.

(** Case inversion, conversion and universe polymorphism. *)
Set Universe Polymorphism.
Inductive IsTy@{i j} : Type@{j} -> SProp :=
  isty : IsTy Type@{i}.

Definition IsTy_rec_red@{i j+} (P:forall T : Type@{j}, IsTy@{i j} T -> Set)
           v (e:IsTy@{i j} Type@{i})
  : IsTy_rec P v _ e = v
  := eq_refl.

(** Sigma in SProp can be done through Squash and relevant sigma. *)
Definition sSigma (A:SProp) (B:A -> SProp) : SProp
  := Squash (@sigT (rBox A) (fun x => rBox (B (runbox _ x)))).

Definition spair (A:SProp) (B:A->SProp) (x:A) (y:B x) : sSigma A B
  := squash _ (existT _ (rbox _ x) (rbox _ y)).

Definition spr1 (A:SProp) (B:A->SProp) (p:sSigma A B) : A
  := let 'squash _ (existT _ x y) := p in runbox _ x.

Definition spr2 (A:SProp) (B:A->SProp) (p:sSigma A B) : B (spr1 A B p)
  := let 'squash _ (existT _ x y) := p in runbox _ y.
(* it's SProp so it computes properly *)

(** Compare blocked invertcase *)
Definition blocked1 (x:nat) (e:sNZ x) (a:nat) :=
  match e with
    snz _ => a
  end.
Definition blocked2 (x:nat) (e:sNZ x) (a:nat) :=
  match e with
    snz _ => 0+a
  end.
Check fun x (e:sNZ x) a => eq_refl : (blocked1 x e a) = (blocked2 x e a).



(** Play with UIP *)
Lemma of_seq {A:Type} {x y:A} (p:seq x y) : x = y.
Proof.
  destruct p. reflexivity.
Defined.

Lemma to_seq {A:Type} {x y:A} (p: x = y) : seq x y.
Proof.
  destruct p. reflexivity.
Defined.

Lemma eq_srec (A:Type) (x y:A) (P:x=y->Type) : (forall e : seq x y, P (of_seq e)) -> forall e, P e.
Proof.
  intros H e. destruct e.
  apply (H (srefl _)).
Defined.

Lemma K : forall {A x} (p:x=x:>A), p = eq_refl.
Proof.
  intros A x. apply eq_srec. intros;reflexivity.
Defined.

Definition K_refl : forall {A x}, @K A x eq_refl = eq_refl
  := fun A x => eq_refl.

Section funext.

  Variable sfunext : forall {A B} (f g : A -> B), (forall x, seq (f x) (g x)) -> seq f g.

  Lemma funext {A B} (f g : A -> B) (H:forall x, (f x) = (g x)) : f = g.
  Proof.
    apply of_seq,sfunext;intros x;apply to_seq,H.
  Defined.

  Definition funext_refl A B (f : A -> B) : funext f f (fun x => eq_refl) = eq_refl
    := eq_refl.
End funext.
