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

Eval compute in (expr_to_iRRAM_function_string "ilog2" [iRRAM_REAL] iRRAM_REAL ilog2).

Section proof.
  Context `{!heapG Σ} (N : namespace).

  Definition ilog2_positive_inv (x : R) (ll ly : loc) : iProp Σ :=
    (∃ (l:Z) (y:R), ll ↦ #l ∗ ly ↦ #y ∗ ⌜(1 < y /\ y * (Rpower 2 (IZR (l - 1))) = x)%R⌝)%I.

  Definition ilog2_negative_inv (x : R) (ll : loc) : iProp Σ :=
    (∃ (l:Z), ll ↦ #l ∗ ⌜(x < (Rpower 2 (IZR l)))%R⌝)%I.


  Lemma ilog2_spec (R : iProp Σ) x:
    {{{ ⌜(x > 0)%R⌝ }}}
      ilog2 (Lit $ LitREAL $ x)
    {{{ l, RET #l; ⌜(Rpower 2 (IZR (l-1)) < x < (Rpower 2 (IZR (l+1))))%R⌝ }}}.
  Proof.
    iIntros (Φ HR) "HΦ". rewrite -wp_fupd /ilog2 /=.
    wp_seq. wp_alloc ll as "Hl". wp_seq.
    wp_bind (_ <(_) _)%E. iApply wp_rlt; eauto.
    iNext. iIntros (v' Hv'). iModIntro.
    inversion_clear Hv'; wp_if.
    - (* if true *)
      wp_alloc ly as "Hy". wp_let.
      iAssert (ilog2_positive_inv x ll ly) with "[Hl Hy]" as "INV".
      { iExists _, _. iFrame. iPureIntro. ria. split; ria. }
      iLöb as "IH". iDestruct "INV" as (l y) "[Hl [Hy %]]". destruct H as [HY HX].
      iApply wp_while. iNext. wp_load. wp_bind (_ <(_) _)%E. iApply wp_rlt; eauto. iNext.
      iIntros (v'' Hv''). iModIntro. inversion_clear Hv''.
      + (* while true *)
        wp_if. wp_load. wp_op. wp_store. wp_seq. wp_load. wp_op; cycle 1.
        { destruct (bool_decide_reflect (2%R = 0%R)); eauto. ria. }
        wp_store. iApply ("IH" with "HΦ").
        iExists _, _. iFrame. iPureIntro. ria. split; ria. rewrite <- HX. ria.
      + (* while false *)
        wp_if. wp_load. iModIntro. iApply "HΦ". iPureIntro. subst. ria.
        rewrite <- Rmult_assoc. rewrite (@Rmult_comm y _). rewrite Rmult_assoc.
        split; eapply Rfourier_lt; ria.
    - (* if false *)
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
