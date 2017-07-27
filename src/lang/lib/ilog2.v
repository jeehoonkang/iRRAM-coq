From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iRRAM.lang Require Import proofmode notation extraction real_lemmas.
Require Import Reals Fourier.
Set Default Proof Using "Type".

Definition ilog2 : expr :=
  λ: "x",
  let: "l" := ref #1 in
  (if: ##(3/2) <(#-1) "x"
   then let: "y" := ref "x" in
        while: (##(5/2) <(#(-1)) !"y")
        do ("l" <- !"l" + #1;; "y" <- !"y" / ##(2))
   else repeat: ("l" <- !"l" - #1)
        until (##3 * ##2 ^ (!"l"-#2)) <(!"l"-#2) "x")
  ;;
  !"l".

Section proof.
  Context `{!heapG Σ} (N : namespace).

  Definition ilog2_positive_inv (x : R) (ll ly : loc) : iProp Σ :=
    (∃ (l:Z) (y:R), ll ↦ #l ∗ ly ↦ #y ∗ ⌜(1 < y /\ y * (Rpower 2 (IZR (l - 1))) = x)%R⌝)%I.

  Definition ilog2_negative_inv (x : R) (ll : loc) : iProp Σ :=
    (∃ (l:Z), ll ↦ #l ∗ ⌜(x < (Rpower 2 (IZR l)))%R⌝)%I.


  Lemma ilog2_spec x:
    {{{ ⌜(x > 0)%R⌝ }}}
      ilog2 (Lit $ LitREAL $ x)
    {{{ l, RET #l; ⌜(Rpower 2 (IZR (l-1)) < x < (Rpower 2 (IZR (l+1))))%R⌝ }}}.
    (* NOTE:
     *
     * Hoare triple {{{ P }}} C {{{ RET l; Q }}}:
     *    if the pre-invariant P holds and C is executed and its result is l,
     *    then the post-invariant Q holds.
     *
     * Please regard ⌜P⌝ as just P, and #x as x.
     *)
  Proof.
    iIntros (Φ HR) "HΦ".
    (* NOTE:
     *
     * 1. Please regard "∗" as "/\", and "-∗" as implication.
     *    Also, please regard "□P", "▷P" as just "P".
     *    (they are separation logic constructs, beyond the scope of this talk)
     *
     * 2. We encode {{{ P }}} C {{{ RET l; Q }}} as follows.
     *
     * First, it can be defined as "P -> WP C Q":
     *    if the pre-invariant P holds,
     *    then the WP C Q (weakest pre-invariant of C for Q) holds.
     *
     * Second, it is actually defined as "forall Φ, P -> (Q -> Φ l) -> WP C Φ":
     *    for any Φ, if the pre-invariant P holds and Q implies Φ,
     *    then the WP C Φ (weakest pre-invariant of C for Φ) holds.
     *)
    rewrite -wp_fupd /ilog2 /=. wp_seq.
    wp_alloc ll as "Hl".
    (* NOTE:
     *
     * (hoare_alloc)
     *
     * ------------------------------------
     * {{{ }}} ref v {{{ RET ll; ll ↦ v }}}
     *
     * "wp_alloc" asserts a points-to assertion "ll ↦ v":
     * the memory location ll points to the value v.
     *)
    wp_seq. wp_bind (_ <(_) _)%E.
    iApply wp_rlt; eauto.
    (* NOTE:
     *
     * (hoare_rlt)
     *
     * forall v, P -> v ∈ (A <E B) -> Q
     * ---------------------------------
     * {{{ P }}} A <E B {{{ RET v; Q }}}
     *
     * (wp_rlt)
     *
     * forall v, v ∈ (A <E B) -> Q
     * ---------------------------
     * WP A <E B {{{ RET v; Q }}}
     *
     * "wp_rlt" captures the nondeterminism of comparison operator.
     * In order to prove the goal, you should prove that
     * for *any* result "v" for "A <E B", the post-invariant Q should hold.
     *)
    iNext. iIntros (v' Hv'). iModIntro.
    inversion_clear Hv'; wp_if.
    - (* if true *)
      (* NOTE:
       *
       * then let: "y" := ref "x" in
       *      while: (##(5/2) <(#(-1)) !"y")
       *      do ("l" <- !"l" + #1;; "y" <- !"y" / ##(2))
       * ;;
       * !"l"
       *)
      wp_alloc ly as "Hy". wp_seq.
      (* NOTE:
       *
       * loop invariant "ilog2_positive_inv" for "while":
       * (1 < y) /\ (y * 2^(l-1) = x)
       *)
      iAssert (ilog2_positive_inv x ll ly) with "[Hl Hy]" as "INV".
      { iExists _, _. iFrame. iPureIntro. ria. split; ria.
        (* NOTE: "ria" is a powerful tactic for solving goals on reals. *)
      }
      iLöb as "IH".
      (* NOTE:
       *
       * "iLöb" is an induction principle:
       * we can suppose that the current goal holds *one step later*.
       * The induction hypothesis IH will be used when the program doens't exit while.
       *
       * (Löb)
       *
       * ▷P -> P   // ▷P: P holds *one step later*
       * -------
       * P
       *)
      iDestruct "INV" as (l y) "[Hl [Hy %]]". destruct H as [HY HX].
      iApply wp_while. iNext.
      wp_load.
      (* NOTE:
       *
       * We have "Hy" : ly ↦ #y,
       * so the load expression "!ly" can be replaced with "y".
       *)
      wp_bind (_ <(_) _)%E.
      iApply wp_rlt; eauto.
      (* NOTE: second inexact comparison operator *)
      iNext. iIntros (v'' Hv''). iModIntro.
      inversion_clear Hv''.
      + (* while true *)
        (* NOTE:
         *
         * while's condition is true.
         * We need to use the induction hypothesis IH.
         *)
        wp_if. wp_load. wp_op.
        wp_store.
        (* NOTE:
         *
         * In order to guarantee that "ll" is a proper memory location,
         * we require "ll ↦ ??" as a pre-invariant.
         * Fortunately, We have "Hl" : ll ↦ #l.
         *)
        wp_seq. wp_load. wp_op; cycle 1.
        { destruct (bool_decide_reflect (2%R = 0%R)); eauto. ria. }
        wp_store.
        iApply ("IH" with "HΦ").
        (* NOTE:
         *
         * We just applied IH! *)
        iExists _, _. iFrame. iPureIntro. ria. split; ria. rewrite <- HX. ria.
      + (* while false *)
        wp_if. wp_load. iModIntro. iApply "HΦ". iPureIntro. subst. ria.
        rewrite <- Rmult_assoc. rewrite (@Rmult_comm y _). rewrite Rmult_assoc.
        split; eapply Rfourier_lt; ria.
    - (* if false *)
      (* NOTE:
       *
       * else repeat: ("l" <- !"l" - #1)
       *      until (##3 * ##2 ^ (!"l"-#2)) <(!"l"-#2) "x")
       * ;;
       * !"l"
       *)
      iAssert (ilog2_negative_inv x ll) with "[Hl]" as "INV".
      { iExists _. iFrame. iPureIntro. ria. }
      iLöb as "IH". iDestruct "INV" as (l) "[Hl %]". rename H into HX.
      iApply wp_repeat. iNext. repeat (try wp_load; try wp_op; try wp_store).
      wp_bind (_ <(_) _)%E. iApply wp_rlt; eauto. iNext.
      iIntros (v'' Hv''). iModIntro. inversion_clear Hv''.
      + (* repeat true *)
        wp_if. wp_load. iModIntro. iApply "HΦ". iPureIntro. ria.
        apply move_lt_rhs in LT.
        rewrite <- (@Rmult_1_l (Rpower 2 (IZR l) * / 2 * / 4)) in LT at 2.
        rewrite <- Rmult_minus_distr_r in LT.
        replace (3 - 1) with 2 in LT; ria. split; ria.
        * eapply Rle_lt_trans; eauto. ria. apply Req_le. ria.
        * rewrite Rmult_assoc. rewrite <- Rinv_l_sym; ria. intro. ria.
      + (* repeat false *)
        wp_if. iApply ("IH" with "HΦ").
        iExists _. iFrame. iPureIntro. ria.
        eapply Rlt_le_trans; eauto. apply Req_le. ria.
  Qed.
End proof.
