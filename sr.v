Require Import List Arith Omega.
Require Import STLC_Ref.term STLC_Ref.ty STLC_Ref.env STLC_Ref.red.

Inductive sub: Ty -> Ty -> Prop :=
 | subArr : forall A B U V, sub U A -> sub B V -> sub (A ⇒ B) (U ⇒ V)
 | subRefl: forall S, sub S S
         (* Really not sure about that one, need to think about it *)
 (* | subRef: forall S T, sub T S -> sub (Ref S) (Ref T) *)
 | subTrans: forall S T U, sub S T -> sub T U -> sub S U
.

Lemma inv_arr_l: forall A B T, sub (A ⇒ B) T -> exists U, exists V,
    T = U ⇒ V /\ sub U A /\ sub B V.
Proof.
intros A B T hsub.
remember (A ⇒ B) as AB.
revert A B HeqAB.
induction hsub as [ ? ? ? ? h1 hi1 h2 hi2 | ? (* | ? ? h hi *) | ? ? ? h1 hi1 h2 hi2];
        intros X Y heq.
- injection heq; intros; subst; clear heq.
  exists U; exists V; now split.
- subst.
  exists X; exists Y; now repeat split; apply subRefl.
(* - discriminate. *)
- subst.
  destruct (hi1 _ _ (eq_refl _)) as [A [B [hA [? ?]]]].
  apply hi2 in hA as [W [Z [ hW [? ?]]]].
  exists W; exists Z; repeat split; [
     assumption |
     now apply subTrans with (T := A) |
     now apply subTrans with (T := B) ].
Qed.

Lemma inv_arr_r: forall A B S, sub S (A ⇒ B) -> exists U, exists V,
    S = U ⇒ V /\ sub A U /\ sub V B.
Proof.
intros A B S hsub.
remember (A ⇒ B) as AB.
revert A B HeqAB.
induction hsub as [ ? ? ? ? h1 hi1 h2 hi2 | ? (* | ? ? h hi *) | ? ? ? h1 hi1 h2 hi2];
        intros X Y heq.
- injection heq; intros; subst; clear heq.
  exists A; exists B; now split.
- subst.
  exists X; exists Y; now repeat split; apply subRefl.
(* - discriminate. *)
- subst.
  destruct (hi2 _ _ (eq_refl _)) as [A [B [hA [? ?]]]].
  apply hi1 in hA as [W [Z [ hW [? ?]]]].
  exists W; exists Z; repeat split; [
     assumption |
     now apply subTrans with (T := A) |
     now apply subTrans with (T := B) ].
Qed.

(* Lemma inv_Ref: forall A T, sub (Ref A) T -> exists U, T = Ref U /\ sub U A. *)
(* Proof. *)
(* intros A T hsub. *)
(* remember (Ref A) as RA. *)
(* revert A HeqRA. *)
(* induction hsub as [ ? ? ? ? h1 hi1 h2 hi2 | ? | ? ? h hi | ? ? ? h1 hi1 h2 hi2]; *)
(*         intros X heq. *)
(* - discriminate. *)
(* - subst. *)
(*   exists X; now split; [ | apply subRefl]. *)
(* - injection heq; intros; subst; clear heq. *)
(*   exists T; now split. *)
(* - subst. *)
(*   destruct (hi1 _ (eq_refl _)) as [A [hA ?]]. *)
(*   apply hi2 in hA as [B [hB ?]]. *)
(*   exists B; split; [ *)
(*      assumption | *)
(*      now apply subTrans with (T := A) ]. *)
(* Qed. *)

Lemma inv_Ref_r_ : forall S T, sub S T -> forall A, T = Ref A -> S = Ref A.
Proof.
induction 1 as [ | ? | ? ? ? h1 hi1 h2 hi2]; intros X heq; 
        [ discriminate | assumption | ].
apply hi1.
now apply hi2.
Qed.

Lemma inv_Ref_l_ : forall S T, sub S T -> forall A, S = Ref A -> T = Ref A.
Proof.
induction 1 as [ | ? | ? ? ? h1 hi1 h2 hi2]; intros X heq; 
        [ discriminate | assumption | ].
apply hi2.
now apply hi1.
Qed.

Lemma inv_Ref_l: forall A T, sub (Ref A) T -> T = Ref A.
Proof.
now intros; apply inv_Ref_l_ with (S := (Ref A)).
Qed.

Lemma inv_Ref_r: forall A S, sub S (Ref A) -> S = Ref A.
Proof.
now intros; apply inv_Ref_r_ with (T := (Ref A)).
Qed.

(* This map is used as truth source to type memories: each address in the
   the map is associated with a typ. The idea is that memories should be
   typed in the empty context, so we get something like:
   
   forall address a in a memory m typed by a type store D,
     nil, D ⊢ Addr a : D(a)
*)
Definition TStore := list (Addrs * Ty).

(* Type store inclusion *)
Definition InclTStore {T: Type} D1 D2 := forall u (t: T),
    readAddr u D1 = Some t -> readAddr u D2 = Some t.

Lemma InclTStore_refl: forall T (D: list (Addrs * T)), InclTStore D D.
Proof.
now intros.
Qed.
 
Lemma app_InclTStore_left: forall {T: Type} (D D1 D2 : list (Addrs * T)),
    InclTStore D D1 -> InclTStore D (D1 ++ D2).
Proof.
intros T D D1 D2 hin x M hx.
apply readAddr_app.
now apply hin.
Qed.

(* Typing judgement for terms. It is STLC extended with references as
 * described in https://www-apr.lip6.fr/~demangeon/Recherche/impfun2.pdf
 * with minor tweaks to be able to mechanism the proofs:
 * - Addition of the type store D instead of having typed variables,
 *   which break the hard mutual dependency between reduction and typing
 * - Subject Reduction is proved in the empty context (as usual for call
 *   by value reductions). This removes the need for memories to be only
 *   values.
 * TODO: try to extend to a full result
 *)
Inductive typ : Env -> TStore -> Term -> Ty -> Prop :=
 | cVar  : forall Γ D A v, A ↓ v ∈ Γ -> typ Γ D (#v) A
 | cLa   : forall Γ D A B M, typ (A::Γ) D M B -> typ Γ D (λ[A], M) (A ⇒ B)
 | cApp  : forall Γ D M N A B, typ Γ D M (A ⇒ B) -> typ Γ D N A ->
         typ Γ D (M • N) B
 | cRef  : forall Γ D M A, typ Γ D M A -> typ Γ D (ref M) (Ref A)
 | cUnit : forall Γ D, typ Γ D unit Unit
 | cAddr : forall Γ D T u, readAddr u D = Some T -> typ Γ D (Addr u) (Ref T)
 | cAsg  : forall Γ D M N A, typ Γ D M (Ref A) -> typ Γ D N A ->
         typ Γ D (M :=: N) Unit 
 | cDrf  : forall Γ D M A, typ Γ D M (Ref A) -> typ Γ D (deref M)  A
 | cSub  : forall Γ D M A B, sub A B -> typ Γ D M A -> typ Γ D M B
.

Hint Constructors typ.

Lemma InclTStore_typ: forall Γ D1 M T, typ Γ D1 M T -> forall D2,
    InclTStore D1 D2 -> typ Γ D2 M T.
Proof.
induction 1 as [ ? ? ? v hin | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        r ? ? ? h hi | ? ? | ? ? ? ? h | ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? ? ? ? hsub h hi ]; intros  D2 hincl; try solve [
            constructor; now apply hi | now constructor
            | econstructor; [now apply hi1 | now apply hi2 ] ].
- constructor.
  now apply hincl.
- apply cSub with (A := A); [ now apply hsub | ].
  now apply hi.
Qed.

(* a type store D types a memory m if they map the same set of addresses
 * and types in D type the corresponding term in m in the empty context *)
Definition WfTStore D mem :=
    (forall u, InAddr u D <-> InAddr u mem) /\
    (* (length D = length mem) /\ *)
    (forall u V, readAddr u mem = Some V ->
        (match readAddr u D with Some T => typ nil D V T | None => False end)).

(** Weakening Property: if a judgement is valid, we can insert a well-typed term
  in the context, it will remain valid. This is where the type checking for
  inserting items in a context is done.*)
Theorem weakening: forall Δ D M T, typ Δ D M T ->
    forall Γ A n Δ', ins_in_env Γ A n Δ Δ' -> typ Δ' D (M ↑ 1 # n) T.
Proof.
induction 1 as [ Δ D ? ? hin | Δ D ? ? ? h hi | Δ D ? ? ? ? h1 hi1 h2 hi2 |
        Δ D ? ? h hi | Δ D | Δ D ? ? ? | Δ D ? ? ? h1 hi1 h2 hi2 |
                Δ D ? ? h hi | Δ D ? ? ? hsub h hi ];
        intros Γ ? n Δ' hins; simpl in *; try solve [
            constructor; eapply hi; constructor; now apply hins |
            constructor; eapply hi; now apply hins |
            econstructor; [now eapply hi1; apply hins |
                           now eapply hi2; apply hins ] ].
- destruct le_gt_dec; constructor.
  + eapply ins_item_ge; [ now apply hins | assumption | assumption].
  + eapply ins_item_lt; [ now apply hins | | ]; assumption.
- now constructor.
- econstructor; [ now apply hsub | ].
  eapply hi.
  now apply hins.
Qed.

Theorem thinning :
   forall Γ D M T A, typ Γ D M T -> typ (A::Γ) D (M ↑ 1) T.
Proof.
intros.
eapply weakening.
- now apply H.
- now constructor.
Qed.

Theorem thinning_n : forall n Δ Δ', trunc n Δ Δ' -> forall D M T,
    typ Δ' D M T -> typ Δ D (M ↑ n)  T.
Proof.
induction n as [ | n hi]; intros Δ Δ' ht D M T hM.
- inversion ht; subst; clear ht.
  now rewrite lift0.
- inversion ht; subst; clear ht.
  change (S n) with (1 + n).
  replace (M ↑ (1+n)) with ((M ↑ n) ↑ 1) by (apply lift_lift).
  apply thinning; trivial.
  eapply hi.
  + now apply H0.
  + assumption.
Qed.

(** Substitution Property: if a judgment is valid and we replace a variable by a
  well-typed term of the same type, it will remain valid.*)
(* begin hide *)
Lemma sub_trunc : forall Δ A n Γ Γ', sub_in_env Δ A n Γ Γ' -> trunc n Γ' Δ.
Proof.
induction 1; now repeat constructor.
Qed.
(* end hide *)

Theorem substitution : forall Γ D M T , typ Γ D M T  ->
    forall Δ P A,  typ Δ D P A ->
 forall Γ' n , sub_in_env Δ A n Γ Γ' -> typ Γ' D (M [ n ←P ])  T.
Proof.
induction 1 as [ ? ? ? v hin | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? | ? ? ? ? ? h1 hi1 h2 hi2 |
                ? ? ? ? h hi | ? ? ? ? ? hs h hi ];
    intros Δ P X hP Γ' n hsub; simpl; try solve [
        now econstructor; [eapply hi1; [apply hP | ] |
                eapply hi2; [apply hP | ]]
        | constructor; now  eapply hi; [ now apply hP | ]].
- destruct lt_eq_lt_dec as [ [] | ].
  + constructor.
    eapply nth_sub_inf; [ now apply hsub | now omega | assumption].
  + subst.
    eapply thinning_n.
    * eapply sub_trunc.
      now apply hsub.
    * replace A with X; [ assumption | ]. 
      eapply nth_sub_eq; [ now apply hsub | assumption].
  + constructor.
    eapply nth_sub_sup; [ now apply hsub | now omega |].
    replace (S (v - 1)) with v by now omega.
    assumption.
- econstructor.
  eapply hi; [ now apply hP | ].
  now constructor.
- now constructor.
- econstructor; [ now apply hs | eapply hi].
  + now apply hP.
  + assumption.
Qed.

(* Adding a fresh variable to a type store doesn't change existing typing 
 * judgements
 *)
Lemma bindAddr_thinning: forall Γ D M T, typ Γ D M T -> forall u S,
    ~ InAddr u D -> typ Γ (bindAddr u S D) M T.
Proof.
induction 1 as [ ? ? ? v ? | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? | ? ? ? ? ? h1 hi1 h2 hi2 | ? ? ? ? h hi
        | ? ? ? ? ? hsub h hi ];
        intros w S hnotin; try solve [
            now constructor |
            now constructor; apply hi |
            now econstructor; [ apply hi1 | apply hi2 ]].
- constructor; simpl.
  destruct Nat.eq_dec; [subst | assumption].
  elim hnotin.
  now apply read2In with T.
- econstructor; [ now apply hsub | ].
  now apply hi.
Qed.

(* Adding a duplicate address with the same type that is already bound in
 * the store doesn't change existing typing judgements
 *)
Lemma bindAddr_thinning_same: forall Γ D M T, typ Γ D M T -> forall u S,
    readAddr u D = Some S -> typ Γ (bindAddr u S D) M T.
Proof.
induction 1 as [ ? ? ? v ? | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? | ? ? ? ? ? h1 hi1 h2 hi2 |
                ? ? ? ? h hi | ? ? ? ? ? hsub h hi ];
        intros w S hr; try solve [
            now constructor |
            now constructor; apply hi |
            now econstructor; [ apply hi1 | apply hi2 ]].
- constructor; simpl.
  destruct Nat.eq_dec; [subst | assumption].
  now elim hr.
- econstructor; [ now apply hsub | ].
  now apply hi.
Qed.
  
Lemma bindWfTStore: forall D mem u V A,
    WfTStore D mem -> typ nil D V A -> ~ InAddr u mem ->
    WfTStore (bindAddr u A D) (bindAddr u V mem).
Proof.
intros D mem u V A [h1 h2] htyp hin; split.
- intros w; split; intro h; simpl in *.
  + destruct Nat.eq_dec; try now idtac.
    now apply h1.
  + destruct Nat.eq_dec; try now idtac.
    now apply h1.
- intros w W hr; simpl in *.
  destruct Nat.eq_dec.
  + injection hr; intros; subst; clear hr.
    apply bindAddr_thinning; [ assumption | ].
    intro h; apply hin; now apply h1.
  + generalize (h2 w W hr).
    destruct (readAddr w D); [ | now idtac ].
    intro h; apply bindAddr_thinning; [ assumption | ].
    intro hh; apply hin; now apply h1.
Qed.

(* Inversion Lemmas *)
Lemma inv_la: forall Γ D A M T, typ Γ D (λ[A], M) T -> exists B,
    sub (A ⇒  B) T /\ typ (A:: Γ) D M B.
Proof.
intros Γ D A M T; remember (λ[A], M) as L; intro typ; revert A M HeqL.
induction typ; intros; try discriminate.
- injection HeqL; intros; subst; clear HeqL.
  now exists B; split; [now apply subRefl | ].
- subst.
  destruct (IHtyp _ _ (eq_refl _)) as [ B0 [h1 h2]].
  exists B0; split; [ | assumption ].
  now apply subTrans with (T := A).
Qed.

Lemma inv_var : forall Γ D x A, typ Γ D #x A -> exists B, sub B A /\ B ↓ x ∈ Γ. 
Proof.
intros Γ D x A htyp; remember #x as X; revert x HeqX.
induction htyp; intros; try discriminate.
- injection HeqX; intros; subst; clear HeqX.
  exists A; intuition.
  now apply subRefl.
- destruct (IHhtyp x HeqX) as (A' & ? & ?); exists A'; split; [ | assumption ].
  now apply subTrans with (T := A).
Qed.

Lemma inv_app : forall Γ D M N T, typ Γ D (M • N) T -> exists A, exists B,
    sub B T /\ typ Γ D M (A ⇒  B) /\ typ Γ D N A.
Proof.
intros Γ D M N T htyp; remember (M • N) as MN; revert M N HeqMN.
induction htyp; intros; try discriminate.
- clear IHhtyp1 IHhtyp2. injection HeqMN; intros; subst; clear HeqMN.
  exists A; exists B; intuition.
  now apply subRefl.
- destruct (IHhtyp M0 N HeqMN) as (K & L & ? & ?& ?); exists K; exists L;
  split; [ now apply subTrans with (T := A) | ].
  split; assumption.
Qed.

Lemma inv_addr: forall Γ D u T, typ Γ D (Addr u) T -> exists U,
    sub (Ref U) T /\ readAddr u D = Some U.
Proof.
intros Γ D u T htyp; remember (Addr u) as AU; revert u HeqAU.
induction htyp; intros; try discriminate.
- injection HeqAU; intros; subst; clear HeqAU.
  exists T; now split; [ now apply subRefl | assumption ].
- subst; destruct (IHhtyp _ (eq_refl _)) as [ U [h1 h2]].
  exists U; split; [ now apply subTrans with (T := A) | ].
  assumption.
Qed.

Lemma inv_ref: forall Γ D M T, typ Γ D (ref M) T -> exists U, sub (Ref U) T /\ typ Γ D M U.
Proof.
intros Γ D M T htyp; remember (ref M) as RM; revert M HeqRM.
induction htyp; intros; try discriminate.
- clear IHhtyp.
  injection HeqRM; intros; subst; clear HeqRM.
  exists A; now split; [ now apply subRefl | assumption ].
- subst; destruct (IHhtyp _ (eq_refl _)) as [ U [h1 h2]].
  exists U; split; [ now apply subTrans with (T := A) | ].
  assumption.
Qed.

(* Subject Reduction *)
(* TODO: clean a bit the script *)
Lemma SR: forall Γ D M T, typ Γ D M T -> forall m1 m2 N,
    Γ = nil -> red M m1 N m2 -> WfTStore D m1 ->
    exists D', (InclTStore D D' /\ WfTStore D' m2 /\ typ Γ D' N T).
Proof.
induction 1 as [ ? ? ? v hin | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? h | ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? ? ? ? hsbu h hi];
          intros m1 m2 Q hgamma hred hst; try solve [
            inversion hred; subst; clear hred; constructor; now apply hi
            ].
- inversion hred; subst; clear hred.
  + exists D; split; [ now apply InclTStore_refl |].
    split; [assumption |].
    apply inv_la in h1 as [B0 [hinv1 hinv2]].
    apply inv_arr_l in hinv1 as [ U[ V[ heq[ hU hV]]]].
    injection heq; intros; subst; clear heq.
    eapply substitution.
    * eapply cSub; [ now apply hV | now apply hinv2 ].
    * eapply cSub; [ now apply hU | now apply h2 ].
    * now constructor. 
  + destruct (hi1 m1 m2 M'  (refl_equal _) H4 hst) as [Q [hQ1 [hQ2 hQ3]]].
    exists Q; split; [assumption | ].
    split; [assumption |].
    econstructor; [ now apply hQ3 | ].
    eapply InclTStore_typ; [ now apply h2 | now apply hQ1 ].
  + destruct (hi2 m1 m2 N' (refl_equal _) H5 hst) as [Q [hQ1 [hQ2 hQ3]]].
    exists Q; split; [assumption | ].
    split; [assumption |].
    econstructor; [ | now apply hQ3 ].
    eapply InclTStore_typ; [ now apply h1 | now apply hQ1 ].
- inversion hred; subst; clear hred.
  + exists (bindAddr u A D); repeat split; try assumption.
    * intros x X hx; simpl.
      destruct Nat.eq_dec as [ heq | hne ]; [ | now assumption].
      subst.
      apply read2In in hx.
      apply hst in hx.
      now elim H0.
    * simpl.
      destruct Nat.eq_dec as [heq | hne]; [now idtac | intro hh].
      now apply hst.
    * simpl.
      destruct Nat.eq_dec as [heq | hne]; [now idtac | intro hh].
      now apply hst.
    * intros w V; simpl.
      destruct Nat.eq_dec as [heq | hne]; intro hh.
      -- injection hh; intros; subst; clear hh.
         apply bindAddr_thinning; [assumption | ].
         intro hin; apply H0; now apply hst.
      -- destruct hst as [h1 h2].
         generalize (h2 w V hh).
         destruct (readAddr w D); [ | now idtac].
         intro hty.
         apply bindAddr_thinning; [assumption | ].
         intro hin; apply H0; now apply h1.
    * constructor; simpl.
      now destruct Nat.eq_dec.
  + destruct (hi m1 m2 M' (refl_equal _) H0 hst) as [Q [h1 [h2 h3]]].
    exists Q; split; [assumption | ].
    split; [assumption |].
    now constructor.
- inversion hred; subst; clear hred.
  + apply inv_addr in h1 as [U [hinv1 hinv2]].
    apply inv_Ref_l in hinv1.
    injection hinv1; intros; subst; clear hinv1.
    exists (bindAddr u U D); repeat split; try assumption.
    * intros x X h; simpl; rewrite h.
      destruct Nat.eq_dec; [ | now idtac].
      now subst; rewrite hinv2 in h.
    * simpl.
      destruct Nat.eq_dec as [heq | hne]; [now idtac | intro hh].
      now apply hst.
    * simpl.
      destruct Nat.eq_dec as [heq | hne]; [now idtac | intro hh].
      now apply hst.
    * intros w V; simpl.
      destruct Nat.eq_dec as [heq | hne]; intro hh.
      -- injection hh; intros; subst; clear hh.
         now apply bindAddr_thinning_same.
      -- destruct hst as [hst1 hst2].
         generalize (hst2 w V hh).
         destruct (readAddr w D); [ | now idtac].
         intro hty.
         now apply bindAddr_thinning_same.
    * now constructor; simpl.
  + destruct (hi1 m1 m2 M' (refl_equal _) H4 hst) as [Q [hQ1 [hQ2 hQ3]]].
    exists Q; split; [assumption | ].
    split; [assumption |].
    econstructor; [ now apply hQ3 | ].
    now apply InclTStore_typ with D.
  + destruct (hi2 m1 m2 N' (refl_equal _) H5 hst) as [Q [hQ1 [hQ2 hQ3]]].
    exists Q; split; [assumption | ].
    split; [assumption |].
    econstructor; [ | now apply hQ3 ].
    now apply InclTStore_typ with D.
- inversion hred; subst; clear hred.
  + apply inv_addr in h as [U [hU ?]].
    apply inv_Ref_l in hU.
    injection hU; intros; subst; clear hU.
    exists D; repeat split; [ now apply InclTStore_refl | | | | ].
    * now intro hh; apply hst.
    * now intro hh; apply hst.
    * intros w V hw.
      destruct hst as [h1 h2].
      apply h2 in hw.
      revert hw.
      now destruct (readAddr w D).
    * destruct hst as [h1 h2].
      apply h2 in H0.
      now rewrite H in H0.
  + destruct (hi m1 m2 M' (refl_equal _) H0 hst) as [Q [h1 [h2 h3]]].
    exists Q; repeat split; try assumption.
    * now intro hh; apply h2.
    * now intro hh; apply h2.
    * intros w V hw.
      now apply h2 in hw.
    * now constructor.
- destruct (hi _ _ _ hgamma hred hst) as [DD [ h1 [h2 h3]]].
  exists DD; split; [assumption | split; [assumption | ]].
  now apply cSub with (A := A).
Qed.

Lemma Progress_sub_la: forall Γ D M T, typ Γ D M T -> forall A B,
    T = A ⇒ B -> is_value M -> Γ = nil -> exists U, exists K,
    M = λ[U], K /\ typ (U::Γ) D K B /\ sub A U.
Proof.
induction 1 as [ ? ? ? v hin | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? h | ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? ? ? hsub h hi]; intros X Y heq hV hG; subst;
                try discriminate; try elim hV.
- now inversion hin.
- injection heq; intros; subst; clear heq hV.
  exists X; exists M; split; [reflexivity | split; [assumption | ]].
  now apply subRefl.
- apply inv_arr_r in h as [U [V [-> [hinvU hinvV]]]].
  destruct (IHhi _ _ (eq_refl _) hV (eq_refl _)) as
     [ Z [ K [ -> [htyp hsub]]]].
  exists Z; exists K; split;[ reflexivity | split].
  + now apply cSub with (A := V).
  + now apply subTrans with (T := U).
Qed.

Lemma Progress_sub_addr: forall Γ D M T, typ Γ D M T -> forall A,
    T = Ref A -> is_value M -> Γ = nil -> exists u,
    M = Addr u /\ readAddr u D = Some A.
Proof.
induction 1 as [ ? ? ? v hin | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? h | ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? ? ? hsub h hi]; intros X heq hV hG; subst;
                try discriminate; try elim hV.
- now inversion hin.
- injection heq; intros; subst; clear heq hV.
  exists u; split; [reflexivity | assumption].
- apply inv_Ref_r in h; subst.
  destruct (IHhi _ (eq_refl _) hV (eq_refl _)) as [ u [ -> h]].
  now exists u; split; [reflexivity | ].
Qed.

Lemma Progress_: forall Γ D M T, typ Γ D M T -> Γ = nil ->
    forall m1, WfTStore D m1 ->
    (exists N, exists m2, red M m1 N m2) \/ is_value M.
Proof.
induction 1 as [ ? ? ? v hin | ? ? ? ? ? h hi | ? ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? | ? ? ? ? h | ? ? ? ? ? h1 hi1 h2 hi2 |
        ? ? ? ? h hi | ? ? ? ? hsub h hi]; intros hgamma m1 hst; try (now right).
- left.
  destruct (hi1 hgamma m1 hst) as [[M' [m2 hred]] | hV].
  + exists (M' • N); exists m2; now constructor.
  + destruct (hi2 hgamma m1 hst) as [[N' [m2 hred]] | hW].
    * exists (M • N'); exists m2; now constructor.
    * destruct (Progress_sub_la _ _ _ _ h1 A B (eq_refl _) hV hgamma) as
      [ U [ K [ -> [ hU htyp]]]].
      now exists (K [← N]); exists m1; constructor.
- left.
  destruct (hi hgamma m1 hst) as [[M' [m2 hred]] | hV].
  + exists (ref M'); exists m2; now constructor.
  + exists (Addr (fresh m1)); exists (bindAddr (fresh m1) M m1);
     constructor; [ | assumption ].
    now apply fresh_is_fresh.
- left. 
  destruct (hi1 hgamma m1 hst) as [[M' [m2 hred]] | hV].
  + exists (M' :=: N); exists m2; now constructor.
  + destruct (hi2 hgamma m1 hst) as [[N' [m2 hred]] | hW].
    * exists (M :=: N'); exists m2; now constructor.
    * apply Progress_sub_addr with (A := A) in h1 as [u [-> hu]];
      [ | reflexivity | assumption | assumption ].
      now exists unit; exists (bindAddr u N m1); constructor.
- left. 
  destruct (hi hgamma m1 hst) as [[M' [m2 hred]] | hV].
  + exists (deref M'); exists m2; now constructor.
  + apply Progress_sub_addr with (A := A) in h as [u [-> hu]];
      [ | reflexivity | assumption | assumption ].
    case_eq (readAddr u m1).
    * now intros V heq; exists V; exists m1; constructor.
    * intro hr; apply read2In in hu.
      apply hst in hu.
      apply In2read in hu as [ ? hh].
      now rewrite hh in hr; discriminate.
- destruct (IHhi hgamma m1 hst) as [[N [m2 hred]] | hV].
  + now left; exists N; exists m2.
  + now right.
Qed.

Lemma Progress: forall D M T, typ nil D M T -> 
    forall m1, WfTStore D m1 ->
    (exists N, exists m2, red M m1 N m2) \/ is_value M.
Proof.
intros D M T htyp m1 h.
eapply Progress_.
- now apply htyp.
- reflexivity.
- assumption.
Qed.
