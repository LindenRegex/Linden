(** * Complexity of the PikeVM algorithm *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeVM PikeSubset Prefix.
From Linden Require Import Correctness PikeEquiv SeenSets.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord.

(* We prove that there is a natural measure that strictly decreases at each step. *)
(* This provides an upper bound on the number of steps needed to reach a final state. *)
(* This upper bound can be expressed in terms of the size of the regex and the size of the input string. *)

Section Complexity.
Context {params: LindenParameters}.
Context (rer: RegExpRecord).
Context {VMS: VMSeen}.

(** * Free slots  *)
(* To define the measure, we need a notion of free slots: how many more states can the PikeVM visit *)

(* well-formedness of a seen set: it was obtained by applying add to the initial seen set *)
(* each element that was added is smaller than some `size` constant (size of the bytecode) *)
(* and `dist` is the no-duplicate list of distinct elements  *)
Inductive wf: seenpcs -> nat -> list (nat * LoopBool) -> Prop :=
| wf_init:
  forall size, wf initial_seenpcs size []
| wf_new:
  forall seen size pc b dist
    (RANGE: pc < size)
    (NEW: inseenpc seen pc b = false)
    (WF: wf seen size dist),
    wf (add_seenpcs seen pc b) size ((pc,b)::dist)
| wf_seen:
  forall seen size pc b dist
    (RANGE: pc < size)
    (SEEN: inseenpc seen pc b = true)
    (WF: wf seen size dist),
    wf (add_seenpcs seen pc b) size dist.

(* The idea of computing the distinct list is that we want the algorithm to be able to switch between any representation *)
(* of the seen set, using the quite weak axiomatization VMSeen *)
(* But we can prove as an invariant that any representation behaves like a ghost no-duplicate list of pairs *)
(* From this list, it's easy to compute the number of elements, and prove that it's total possible number of element is bounded *)
Lemma wf_in:
  forall seen size dist,
    wf seen size dist ->
    forall pc b,
      inseenpc seen pc b = true <-> In (pc, b) dist.
Proof.
  intros seen size dist H. induction H; intros.
  - rewrite initial_nothing_pc. split; intros; inversion H.
  - rewrite inpc_add. split; intros; destruct H0; simpl; auto;
      right; apply IHwf; auto.
  - rewrite inpc_add. split; intros;
      try destruct H0; try inversion H0; simpl; auto;
      try right; apply IHwf; auto.
Qed.

Lemma wf_nodup:
  forall seen size dist,
    wf seen size dist -> NoDup dist.
Proof.
  intros seen size dist H. induction H; auto.
  { constructor. }
  apply wf_in with (pc:=pc) (b:=b) in H.
  constructor; auto.
  rewrite <- H. rewrite NEW. auto.
Qed.

(* every element is smaller than the size *)
Lemma wf_small:
  forall seen size dist pc b,
    wf seen size dist ->
    In (pc, b) dist ->
    pc < size.
Proof.
  intros seen size dist pc b WF IN. induction WF; auto.
  - inversion IN.
  - destruct IN as [IN|IN]; try inversion IN; subst; auto.
Qed.

(* We will show the dist list is a subset of the following list of all possible elements in a certain range *)
Fixpoint possible_elements (size:nat) :=
  match size with
  | 0 => []
  | S n => (n,CanExit)::(n,CannotExit)::(possible_elements n)
  end.

Lemma possible_size:
  forall size, length (possible_elements size) = 2 * size.
Proof.
  intros size. induction size; auto. simpl. lia.
Qed.

Lemma possible_all:
  forall pc b size,
    pc < size -> In (pc, b) (possible_elements size).
Proof.
  intros pc b size H. induction size; [lia|].
  assert (pc = size \/ pc < size) by lia. destruct H0.
  - subst. simpl. destruct b; auto.
  - apply IHsize in H0. simpl. auto.
Qed.

Theorem wf_size:
  forall seen size dist,
    wf seen size dist -> length dist <= 2 * size.
Proof.
  intros seen size dist H. rewrite <- possible_size.
  apply NoDup_incl_length.
  { eapply wf_nodup; eauto. }
  unfold incl. intros [pca ba] IN.
  eapply wf_small in IN; eauto. apply possible_all. auto.
Qed.

(* the number of free slots in a seen set *)
(* the total number of slots is 2 times the size of the code: each label can be added with 2 possible LoopBool values *)
(* we remove the number of distinct entries in the seen set *)
Definition free (codesize:nat) (dist:list (nat*LoopBool)) : nat :=
  (2 * codesize) - length dist.

Lemma free_initial:
  forall codesize, free codesize [] = 2 * codesize.
Proof.
  intros codesize. unfold free. simpl. lia.
Qed.

Lemma free_add:
  forall seen size dist t,
    wf seen size dist ->
    seen_thread seen t = false ->
    fst (fst t) < size ->
    wf (add_thread seen t) size ((fst (fst t),snd t)::dist).
Proof.
  intros seen size count [[pc gm] b] WF SEEN SIZE. unfold seen_thread in SEEN.
  constructor; auto.
Qed.

(** * Well Formedness Invariant and Measure of PikeVM states *)

(* we add 1 because we consider that even at the last position, there is work to do to reach the final state *)
Definition inpsize (i:input) : nat :=
  match i with
  | Input next pref => 1 + length next
  end.

Lemma inpsize_strict:
  forall i, inpsize i > 0.
Proof.
  intros [next pref]. simpl. lia.
Qed.

Definition size (c:code) : nat := length c.

(* The number of free slots decreases at most steps *)
(* In some cases (a fork), a new thread is created but the number of free slots decreases: this is why free slots are multiplied by 2 *)
(* As we change characters, the seen set might get 2*codesize new free slots (multiplied by 2 for the measure) *)
(* But the input decreases, which makes the measure also decrease, because input size is multiplied by (2 + 4*codesize)  *)
(* It's (2 + 4*codesize) because we might generate a new thread at each input (for unanchored search) and because of the step it takes to advance *)
Definition measure (codesize:nat) (dist:list (nat*LoopBool)) (active blocked:list thread) (inp:input) :=
  (2 * free codesize dist) + length active + length blocked + (inpsize inp * (2 + 4 * codesize)).

(* The invariant that is preserved through pikeVM execution, with a measure that strictly decreases *)
Inductive vm_inv (c:code): pike_vm_state -> nat -> Prop :=
| inv_final:
  forall b, vm_inv c (PVS_final b) 0
| inv_pvs:
  forall inp active best blocked nextprefix seen dist
    (* the threads in active and blocked have their pc inside the code range *)
    (ACTIVEWF: forall t, In t active -> fst (fst t) < size c)
    (BLOCKEDWF: forall t, In t blocked -> fst (fst t) < size c)
    (* the seen set is well-formed, and has `count` distinct elements *)
    (SEENWF: wf seen (size c) dist)
    (* The next place where the prefix can match is in range of the input *)
    (RANGEPREF: forall n lit strs, nextprefix = Some (n, lit, strs) -> inpsize inp > S n),
    vm_inv c (PVS inp active best blocked nextprefix seen) (measure (size c) dist active blocked inp).

Lemma nonfinal_pos:
  forall c inp active best blocked nextprefix seen m,
    vm_inv c (PVS inp active best blocked nextprefix seen) m -> 0 < m.
Proof.
  intros c inp active best blocked nextprefix seen m H. inversion H. subst. unfold measure.
  specialize (inpsize_strict inp) as SIZE. lia.
Qed.

(** * Next prefix search is in range  *)

Theorem search_in_range:
  forall inp lit n lit' (strs:StrSearch) strs',
    @next_prefix_counter _ strs inp lit = Some (n, lit', strs') ->
    inpsize inp > S n.
Proof.
  intros [next pref] lit n lit' strs strs' H. unfold next_prefix_counter in H.
  destruct next; simpl in H. inversion H.
  destruct str_search eqn:SEARCH; inversion H; subst.
  apply str_search_bound in SEARCH. simpl. lia.
Qed.

Lemma advance_inpsize:
  forall inp1 inp2 n,
    advance_input inp1 forward = Some inp2 ->
    inpsize inp1 > S n ->
    inpsize inp2 > n.
Proof.
  intros [next1 pref1] inp2 n H H0. simpl in H.
  destruct next1; inversion H.
  simpl in H0. simpl. lia.
Qed.

Lemma advance_S_n:
  forall n next pref c,
    advance_input_n (Input (c::next) pref) (S n) forward =
      advance_input_n (Input next (c::pref)) n forward.
Proof.
  intros n next pref c. simpl. f_equal. rewrite <- app_assoc. auto.
Qed.

Lemma advance_n_inpsize:
  forall inp n,
  inpsize inp > S n ->
  inpsize (advance_input_n inp (S n) forward) < inpsize inp.
Proof.
  intros [next pref] n H.
  generalize dependent next. generalize dependent pref.
  induction n; intros.
  - unfold advance_input_n. destruct next; simpl in H; simpl; lia.
  - destruct next as [|c next]; simpl in H. lia.
    assert (S (length next) > S n) by lia.
    specialize (IHn (c::pref) next H0). rewrite advance_S_n.
    simpl in IHn. simpl. lia.
Qed.


(** * Well-formedness of the code  *)

(* first, we show the code is non empty, ensuring that threads generated by prefix acceleration are in range *)
Definition nonempty (c:code) : Prop := size c > 0.

(* Even if the regex is epsilon, adding the accept instruction makes the code non-empty *)
Lemma compilation_nonempty:
  forall r, nonempty (compilation r).
Proof.
  intros. unfold compilation. destruct compile. unfold nonempty, size.
  rewrite app_length. simpl. lia.
Qed.

(* Some bytecode is well-formed if every target label belongs in some range *)
Definition code_wf (c:code) (size:nat) :=
  forall pc i next,
    get_pc c pc = Some i ->
    In next (next_pcs pc i) ->
    next < size.

Lemma nfa_wf:
  forall r c startl endl pc next i,
    nfa_rep r c startl endl ->
    pc >= startl ->
    pc < endl ->
    get_pc c pc = Some i ->
    In next (next_pcs pc i) ->
    next <= endl.
Proof.
  intros r c startl endl pc next i REP GE LT GET IN.
  generalize dependent pc. induction REP; intros.
  - lia.
  (* char *)
  - assert (pc = lbl) by lia. subst.
    rewrite CONSUME in GET. inversion GET. subst.
    simpl in IN. destruct IN; lia.
  - apply nfa_rep_incr in REP1 as INCR1.
    apply nfa_rep_incr in REP2 as INCR2.
    assert (pc = start \/ pc >= S start) as [ST|H] by lia.
    (* Fork *)
    { subst. rewrite FORK in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|[IN|IN]]; inversion IN; lia. }
    assert (pc < end1 \/ pc >= end1) as [R1|H1] by lia.
    (* in r1 *)
    { eapply IHREP1 in IN; eauto. lia. }
    assert (pc = end1 \/ pc >= S end1) as [J|H2] by lia.
    (* the jmp *)
    { subst. rewrite JMP in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN. lia. }
    (* in r2 *)
    apply IHREP2 in IN; auto.
  - apply nfa_rep_incr in REP1 as INCR1.
    apply nfa_rep_incr in REP2 as INCR2.
    assert (pc < end1 \/ pc >= end1) as [H1|H2] by lia.
    (* in r1 *)
    { apply IHREP1 in IN; auto. lia. }
    (* in r2 *)
    apply IHREP2 in IN; auto.
  - lia.
  - apply nfa_rep_incr in REP as INC.
    assert (pc = start \/ pc >= S start) as [FOR|H] by lia.
    (* fork *)
    { subst. rewrite FORK in GET. destruct greedy; inversion GET; subst;
        simpl in IN; destruct IN as [IN|[IN|IN]]; inversion IN; lia. }
    assert (pc = S start \/ pc >= S (S start)) as [BEG|H1] by lia.
    (* Begin *)
    { subst. rewrite BEGIN in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN; lia. }
    assert (pc = S (S start) \/ pc >= S (S (S start))) as [RES|H2] by lia.
    (* Reset *)
    { subst. rewrite RESET in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN; lia. }
    assert (pc < end1 \/ pc = end1) as [R1|H3] by lia.
    (* in r1 *)
    { apply IHREP in IN; auto. }
    (* endloop *)
    subst. rewrite END in GET. inversion GET. subst.
    simpl in IN. destruct IN as [IN|IN]; inversion IN; lia.
  - apply nfa_rep_incr in REP as INC.
    assert (pc = start \/ pc >= S start) as [FOR|H] by lia.
    (* fork *)
    { subst. rewrite FORK in GET. destruct greedy; inversion GET; subst;
        simpl in IN; destruct IN as [IN|[IN|IN]]; inversion IN; lia. }
    assert (pc = S start \/ pc >= S (S start)) as [BEG|H1] by lia.
    (* Begin *)
    { subst. rewrite BEGIN in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN; lia. }
    assert (pc = S (S start) \/ pc >= S (S (S start))) as [RES|H2] by lia.
    (* Reset *)
    { subst. rewrite RESET in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN; lia. }
    assert (pc < end1 \/ pc = end1) as [R1|H3] by lia.
    (* in r1 *)
    { apply IHREP in IN; auto. }
    (* endloop *)
    subst. rewrite END in GET. inversion GET. subst.
    simpl in IN. destruct IN as [IN|IN]; inversion IN; lia.
  - apply nfa_rep_incr in REP as INC.
    assert (pc = start \/ pc >= S start) as [ST|H] by lia.
    (* open *)
    { subst. rewrite OPEN in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN; lia. }
    assert (pc = end1 \/ pc < end1) as [END|H1] by lia.
    (* close *)
    { subst. rewrite CLOSE in GET. inversion GET. subst.
      simpl in IN. destruct IN as [IN|IN]; inversion IN; lia. }
    (* in r1 *)
    apply IHREP in IN; auto.
  - assert (pc = lbl) by lia. subst.
    rewrite CHECK in GET. inversion GET. subst.
    simpl in IN. destruct IN; lia.
  - assert (pc = lbl) by lia. subst.
    rewrite KILL in GET. inversion GET. subst.
    simpl in IN. inversion IN.
Qed.

Theorem compiled_wf:
  forall r, code_wf (compilation r) (size (compilation r)).
Proof.
  intros r.  destruct (compile r 0) as [c endl] eqn:COMP.
  eapply compile_nfa_rep with (prev:=[]) in COMP as REP; simpl in *; auto.
  unfold compilation. rewrite COMP. unfold code_wf.
  apply fresh_correct in COMP as FRESH. simpl in FRESH. subst.
  intros pc i next GET IN.
  assert (HL: pc < length (c ++ [Accept])).
  { eapply nth_error_Some. unfold get_pc in GET. rewrite GET. intros HI. inversion HI. }
  rewrite app_length in HL. simpl in HL.
  assert (pc = length c \/ pc < length c) as [ACC|H1] by lia.
  (* accept *)
  { subst. assert (get_pc (c ++ [Accept]) (length c) = get_pc [Accept] 0).
    - apply get_first.
    - unfold get_pc in H. simpl in H. unfold get_pc in GET. rewrite H in GET.
      inversion GET. subst. inversion IN. }
  (* inside the code *)
  assert (GETI: get_pc c pc = Some i).
  { unfold get_pc in GET. rewrite nth_error_app1 in GET; auto. }
  assert (POS: pc >= 0) by lia.
  specialize (nfa_wf r c 0 (length c) pc next i REP POS H1 GETI IN) as WF.
  unfold size. rewrite app_length. simpl. lia.
Qed.

Lemma eps_step_blocked_wf:
  forall t code inp newt,
    epsilon_step rer t code inp = EpsBlocked newt ->
    exists i, get_pc code (fst (fst t)) = Some i /\
           In (fst (fst newt)) (next_pcs (fst (fst t)) i).
Proof.
  unfold epsilon_step. intros [[pc gm]b] code inp newt H.
  destruct (get_pc code pc) eqn:GET; [|inversion H].
  destruct b0; inversion H; subst.
  - destruct (check_read rer c inp forward); inversion H1; subst.
    simpl; eexists; split; eauto; simpl; auto; lia.
  - destruct (anchor_satisfied rer a inp); inversion H1; subst.
  - destruct b; inversion H1.
Qed.

Lemma eps_step_active_wf:
  forall t code inp next newt,
    epsilon_step rer t code inp = EpsActive next ->
    In newt next ->
    exists i, get_pc code (fst (fst t)) = Some i /\
           In (fst (fst newt)) (next_pcs (fst (fst t)) i).
Proof.
  unfold epsilon_step. intros [[pc gm] b] code inp next newt H IN.
  destruct (get_pc code pc) eqn:GET.
  2: { inversion H. subst. inversion IN. }
  destruct b0; inversion H; subst;
    try solve[inversion IN; subst; try solve [inversion H0];
              simpl; eexists; split; eauto; simpl; auto; lia].
  - destruct (check_read rer c inp forward); inversion H1; subst;
      inversion IN; subst; try solve [inversion H0];
      simpl; eexists; split; eauto; simpl; auto; lia.
  - destruct (anchor_satisfied rer a inp); inversion H1; subst;
      inversion IN; subst; try solve [inversion H0];
      simpl; eexists; split; eauto; simpl; auto; lia.
  - inversion IN; [|inversion H0]; subst; try solve [inversion H1];
      simpl; eexists; split; eauto; simpl; auto.
  - destruct b; subst; inversion H1; subst;
      inversion IN; subst; try solve [inversion H0];
      simpl; eexists; split; eauto; simpl; auto; lia.
Qed.


(** * PikeVM measure decreases *)

(* epsilon_step cannot generate too many new threads *)
Lemma eps_step_active:
  forall t code inp next,
    epsilon_step rer t code inp = EpsActive next ->
    length next <= 2.
Proof.
  unfold epsilon_step. intros [[pc gm] b] code inp next H.
  destruct (get_pc code pc) eqn:GET.
  2: { inversion H. simpl. lia. }
  destruct b0; try solve [inversion H; simpl; lia].
  - destruct (check_read rer c inp forward); try solve [inversion H; simpl; lia].
  - destruct (anchor_satisfied rer a inp); try solve [inversion H; simpl; lia].
  - destruct b; try solve [inversion H; simpl; lia].
Qed.

Lemma advance_input_decreases:
  forall i1 i2,
    advance_input i1 forward = Some i2 ->
    inpsize i2 < inpsize i1.
Proof.
  intros [n1 p1] [n2 p2] H. simpl in H. destruct n1 as [|h1 n1]; inversion H; subst. simpl. lia.
Qed.

Theorem increase_mult:
  forall a b x,
    a < b ->
    x + a * (S x) < b * (S x).
Proof.
  intros a b c H. repeat rewrite PeanoNat.Nat.mul_succ_r.
  induction c; try lia.
Qed.


(* at each step, the measure strictly decreases *)
(* the well-formedness of the seen set is preserved *)
Theorem pikevm_decreases:
  forall code pvs1 pvs2 m1,
    code_wf code (size code) ->
    nonempty code ->
    pike_vm_step rer code pvs1 pvs2 ->
    vm_inv code pvs1 m1 ->
    exists m2, vm_inv code pvs2 m2 /\ m2 < m1.
Proof.
  intros code pvs1 pvs2 m1 CODEWF NONEMPTY STEP INV. inversion STEP; subst; simpl measure; inversion INV; subst;
    try destruct t as [[pc gm] b].
  (* when reaching a final state, we end up with a measure of 0, while the previous measure was strictly positive *)
  - exists 0. split.
    + constructor.
    + apply nonfinal_pos in INV. auto.
  (* acc: we might add (2*codesize) free slots, but we lose at least one input length *)
  - specialize (RANGEPREF n lit strs eq_refl).
    exists (measure (size code) [] [pike_vm_initial_thread] [] (advance_input_n inp (S n) forward)). split; [constructor|]; auto.
    + (* the new generated thread is in range because the code is nonempty *)
      intros t H. inversion H as [IN1|IN2]; auto.
      subst. unfold pike_vm_initial_thread. simpl. auto.
    + constructor.
    + intros n0 lit0 strs0 H. eapply search_in_range with (strs:=strs); eauto.
    + unfold measure. simpl. rewrite free_initial. specialize (advance_n_inpsize inp n RANGEPREF)as ADV.
      apply increase_mult with (x:= 4 * size code) in ADV as NEXT. simpl in NEXT. lia.
  (* end *)
  - exists 0. split.
    + constructor.
    + apply nonfinal_pos in INV. auto.
  (* nextchar: we might add (2*codesize) free slots, but we lose an input length *)
  - exists (measure (size code) [] (thr::blocked) [] inp2). split; [constructor|]; auto.
    + constructor.
    + intros n lit strs H; inversion H.
    + unfold measure. simpl. rewrite free_initial. apply advance_input_decreases in ADVANCE.
      apply increase_mult with (x:= 4 * size code) in ADVANCE as NEXT. simpl in NEXT. lia.
  (* nextchar_generate: we might add (2*codesize) free slots, but we lose an input length *)
  - exists (measure (size code) [] ((thr::blocked)++[pike_vm_initial_thread]) [] inp2). split; [constructor|]; auto.
    + (* the new generated thread is in range because the code is nonempty *)
      intros t H. apply in_app_or in H as [IN1|IN2]; auto.
      inversion IN2; inversion H. unfold pike_vm_initial_thread. simpl. auto.
    + constructor.
    + intros n lit0 H. eapply search_in_range; eauto.
    + unfold measure. simpl. rewrite free_initial. apply advance_input_decreases in ADVANCE.
      apply increase_mult with (x:= 4 * size code) in ADVANCE as NEXT. simpl in NEXT.
      rewrite app_length. simpl. lia.
  (* nextchar_filter: we might add (2*codesize) free slots, but we lose an input length *)
  - exists (measure (size code) [] (thr::blocked) [] inp2). split; [constructor|]; auto.
    + constructor.
    + intros n0 lit0 strs0 H. inversion H; subst. specialize (RANGEPREF (S n0) lit0 strs0 eq_refl).
      eapply advance_inpsize; eauto.
    + unfold measure. simpl. rewrite free_initial. apply advance_input_decreases in ADVANCE.
      apply increase_mult with (x:= 4 * size code) in ADVANCE as NEXT. simpl in NEXT. lia.
  (* skip: we lose a thread *)
  - exists (measure (size code) dist active blocked inp). split; [constructor|]; auto.
    + intros t0 H. apply ACTIVEWF. simpl. right. auto.
    + unfold measure. simpl. lia.
  (* active: we may add a new thread, but lose a free slot *)
  - assert (RANGE: pc < size code).
    { specialize (ACTIVEWF (pc,gm,b) ltac:(simpl;left;auto)). simpl in ACTIVEWF. auto. }
    exists (measure (size code) ((pc,b)::dist) (nextactive++active) blocked inp). split; [constructor|]; auto.
    + intros t0 H. apply in_app_or in H as [H|H].
      * eapply eps_step_active_wf in STEP0 as [i [GET IN]]; eauto.
      * apply ACTIVEWF. right. auto.
    + unfold add_thread. apply wf_new; auto.
    + specialize (free_add seen (size code) dist (pc,gm,b) SEENWF UNSEEN) as FREE.
      apply wf_size in FREE; auto. apply eps_step_active in STEP0.
      unfold measure, free. rewrite app_length. simpl. simpl in FREE. lia.
  (* match: we lose a thread and a free slot *)
  - assert (RANGE: pc < size code).
    { specialize (ACTIVEWF (pc,gm,b) ltac:(simpl;left;auto)). simpl in ACTIVEWF. auto. }
    exists (measure (size code) ((pc,b)::dist) [] blocked inp). split; [constructor|]; auto.
    + intros t0 H. inversion H.
    + unfold add_thread. apply wf_new; auto.
    + intros n lit strs H; inversion H.
    + specialize (free_add seen (size code) dist (pc,gm,b) SEENWF UNSEEN RANGE) as FREE.
      apply wf_size in FREE. unfold measure, free. simpl. lia.
  (* blocked: we switch an active thread to blocked, but lose a free slot *)
  -  assert (RANGE: pc < size code).
     { specialize (ACTIVEWF (pc,gm,b) ltac:(simpl;left;auto)). simpl in ACTIVEWF. auto. }
     exists (measure (size code) ((pc,b)::dist) active (blocked++[newt]) inp). split; [constructor|]; auto.
     + intros t0 H. apply ACTIVEWF. simpl. right. auto.
     + intros t0 H. apply in_app_or in H as [H|H].
       * eapply BLOCKEDWF; eauto.
       * inversion H; [|inversion H0]. subst.
         eapply eps_step_blocked_wf in STEP0 as [i [GET IN]]; eauto.
     + unfold add_thread. apply wf_new; auto.
     + specialize (free_add seen (size code) dist (pc,gm,b) SEENWF UNSEEN RANGE) as FREE.
       apply wf_size in FREE. unfold measure, free. rewrite app_length. simpl. simpl in FREE. lia.
Qed.

(** * Code Size  *)

(* Here we prove that the size of the NFA bytecode is linear in the size of the regex *)
(* Note that this "size of the regex" counts counted quantifier as being unfolded, so it might not be linear in the size of the textual representation of the regex *)

(* the exact size of the bytecode *)
Fixpoint compsize (r:regex) : nat :=
  match r with
  | Epsilon => 0
  | Regex.Character _ => 1
  | Disjunction r1 r2 => 2 + compsize r1 + compsize r2
  | Sequence r1 r2 => compsize r1 + compsize r2
  | Quantified g 0 (NoI.N 0) r1 => 0
  | Quantified g 0 (NoI.N 1) r1 => 4 + compsize r1
  | Quantified g 0 (NoI.Inf) r1 => 4 + compsize r1
  | Group _ r1 => 2 + compsize r1
  | Anchor _ => 1
  | _ => 0
  end.

Definition codesize (r:regex) := S (compsize r).

Lemma compile_size:
  forall r start endl code,
    pike_regex r ->
    compile r start = (code, endl) ->
    length (code) = compsize r.
Proof.
  intros r start endl code SUBSET COMP.
  generalize dependent start. generalize dependent endl. generalize dependent code.
  induction r; simpl; intros;
    try solve [inversion COMP; subst; auto]; try solve[pike_subset].
  - destruct (compile r1 (S start)) eqn:C1. destruct (compile r2 (S l)) eqn:C2.
    erewrite <- IHr1; eauto. 2: pike_subset.
    erewrite <- IHr2; eauto. 2: pike_subset.
    inversion COMP. subst. simpl. rewrite app_length. simpl. lia.
  - destruct (compile r1 start) eqn:C1. destruct (compile r2 l) eqn:C2.
    erewrite <- IHr1; eauto. 2: pike_subset.
    erewrite <- IHr2; eauto. 2: pike_subset.
    inversion COMP. subst. simpl. rewrite app_length. simpl. lia.
  - destruct min; destruct (destruct_delta delta) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]]; subst; try solve[pike_subset].
    + inversion COMP. auto.
    + destruct (compile r (S (S (S start)))) eqn:C1.
      erewrite <- IHr; eauto. 2: pike_subset.
      inversion COMP. subst. simpl. rewrite app_length. simpl. lia.
    + destruct (compile r (S (S (S start)))) eqn:C1.
      erewrite <- IHr; eauto. 2: pike_subset.
      inversion COMP. subst. simpl. rewrite app_length. simpl. lia.
    + inversion SUBSET; subst; lia.
  - destruct (compile r (S start)) eqn:C1.
    erewrite <- IHr; eauto. 2: pike_subset.
    inversion COMP. subst. simpl. rewrite app_length. simpl. lia.
Qed.

Theorem compilation_size:
  forall r,
    pike_regex r ->
    size (compilation r) = codesize r.
Proof.
  unfold codesize, size, compilation. intros r H. destruct (compile r 0) eqn:COMP.
  apply compile_size in COMP; auto. rewrite <- COMP. rewrite app_length. simpl. lia.
Qed.

(* relating this compilation size to the size of the regex *)
Theorem compsize_regex_size:
  forall (r:regex),
    S (compsize r) <= 4 * (regex_size r).
Proof.
  intros r. induction r; simpl; try lia.
  - destruct min; simpl; [|lia].
    destruct delta; simpl; [|lia].
    destruct n; simpl; [lia|].
    destruct n; simpl; lia.
Qed.

Corollary comp_size_regex_size:
  forall r, pike_regex r ->
    size (compilation r) <= 4 * (regex_size r).
Proof.
  intros r SUBSET. rewrite compilation_size; auto.
  unfold codesize. apply compsize_regex_size.
Qed.

(** * Initial PikeVM Measure *)

Definition complexity (r:regex) (inp:input) : nat :=
  1 + (4 * codesize r) + (inpsize inp * (2 + 4 * codesize r)).

Theorem initial_measure:
  forall inp r,
    pike_regex r ->
    vm_inv (compilation r) (pike_vm_initial_state inp) (complexity r inp).
Proof.
  intros inp r SUBSET.
  replace (complexity r inp) with (measure (codesize r) [] [(0, GroupMap.empty, CanExit)] [] inp).
  - unfold pike_vm_initial_state. rewrite <- compilation_size; auto.
    constructor; auto.
    + intros t H. destruct H. 2: inversion H.
      subst. simpl. unfold compilation. destruct (compile r 0) eqn:C. unfold size. rewrite app_length.
      simpl. lia.
    + intros t H. inversion H.
    + constructor.
    + intros n lit strs H; inversion H.
  - unfold complexity, measure. rewrite <- compilation_size; auto. simpl.
    rewrite free_initial. simpl. lia.
Qed.

(** * Bounding the number of PikeVM steps  *)

(* A counted transitive reflexive cloture relation *)
(* The nat indicates a maximum number of steps *)
Inductive steps {A:Type} (R: A -> A -> Prop): A -> nat -> A -> Prop:=
| steps_refl: forall a n, steps R a n a
| steps_cons:
  forall x y z n
    (STEP: R x y)
    (TRC: steps R y n z),
    steps R x (S n) z.

Lemma steps_trc:
  forall A (R:A->A->Prop) (x y:A) n,
    steps R x n y -> @trc _ R x y.
Proof.
  intros A R x y n H. induction H; econstructor; eauto.
Qed.

Lemma trc_steps:
  forall A (R:A->A->Prop) (x y:A),
    @trc _ R x y -> exists n, steps R x n y.
Proof.
  intros A R x y H. induction H; try destruct IHtrc; eexists;
    try eapply steps_refl with (n:=0); (* avoiding the shelved goal *)
    econstructor; eauto.
Qed.

Lemma more_steps:
  forall A (R:A->A->Prop) x y n m,
    n <= m ->
    steps R x n y ->
    steps R x m y.
Proof.
  intros A R x y n m LE STEPS. generalize dependent m.
  induction STEPS; intros.
  - constructor.
  - destruct m as [|m]; try lia.
    econstructor; eauto. apply IHSTEPS. lia.
Qed.

Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros H n; enough (H0: forall p, p <= n -> P p).
    - apply H0, le_n.
    - induction n; intros; apply H; intros; try lia.
      apply IHn; lia.
Qed.

Lemma pike_vm_bound:
  forall pvs code n,
    code_wf code (size code) ->
    nonempty code ->
    vm_inv code pvs n ->
    exists result, steps (pike_vm_step rer code) pvs n (PVS_final result).
Proof.
  intros pvs code n WF NONEMPTY INV. generalize dependent pvs. induction n using (strong_ind); intros.
  destruct pvs.
  2: { exists best. constructor. }
  specialize (pikevm_progress rer code inp active best blocked nextprefix seen) as [next STEP].
  specialize (pikevm_decreases code (PVS inp active best blocked nextprefix seen) next n WF NONEMPTY STEP INV) as [newm [INV2 DECR]].
  specialize (H newm DECR next INV2) as [result STEPS].
  exists result. apply more_steps with (n:=S newm); try lia.
  econstructor; eauto.
Qed.

(** * Complexity Theorem  *)

Theorem pikevm_complexity:
  forall (r:regex) (inp:input),
    (* for any supported regex r and input inp *)
    pike_regex r ->
    (* The initial state reaches a final state in at most (complexity r inp) steps. *)
    exists result, steps (pike_vm_step rer (compilation r))
                (pike_vm_initial_state inp) (complexity r inp) (PVS_final result).
Proof.
  intros r inp SUBSET.
  apply pike_vm_bound.
  - apply compiled_wf.
  - apply compilation_nonempty.
  - apply initial_measure. auto.
Qed.


(** * Termination of the PikeVM algorithm  *)

(* As a corollary, we can deduce that the PikeVM always terminate *)
Theorem pike_vm_terminates:
  forall r inp,
    pike_regex r ->
    exists result, trc_pike_vm rer (compilation r) (pike_vm_initial_state inp) (PVS_final result).
Proof.
  intros r inp H. eapply pikevm_complexity in H as [result STEPS]; eauto.
  exists result. eapply steps_trc; eauto.
Qed.


End Complexity.
