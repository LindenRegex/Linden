From Linden Require Export ProofSetup ForcedQuant RegexpTree.
From Linden.Rewriting Require Import Examples.

Section EquivalenceChain.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* The chain of equivalences that is defined in the paper *)
  
Theorem equivalence_chain:
  forall r min0 min1 Delta1 Delta2,
    (* when r defines no groups *)
    def_groups r = [] ->

    (* r{min,0,0,false} *)
    (Sequence (Quantified false min0 0 r)
       (* r{min1,Delta1,true} *)
       (Sequence (Quantified true min1 Delta1 r)
          (* r{0,Delta2,true} *)
          (Quantified true 0 Delta2 r)))

      (* is equivalent, for the forward direction, to *)
      ≅[rer][forward]

      (* r{min0+min1,Delta1+Delta2,true} *)
      (Quantified true (min0+min1) (Delta1+Delta2)%NoI r).
Proof.
  intros r min0 min1 Delta1 Delta2 NOGROUPS.
  (* transforms the false into a true *)
  etransitivity.
  { apply seq_equiv. symmetry. apply forced_equiv. reflexivity. }
  (* splits r {min1,Delta1} in two *)
  etransitivity.
  { apply seq_equiv_dir. reflexivity. apply seq_equiv_dir.
    - symmetry. apply bounded_atmost_equiv. auto.
    - reflexivity. }
  (* associativity of the sequence *)
  etransitivity.
  { apply seq_equiv. reflexivity. symmetry. apply sequence_assoc_equiv. }
  etransitivity.
  { apply sequence_assoc_equiv. }
  (* merges the first two, and last two, quantifiers *)
  etransitivity.
  { apply seq_equiv.
    - apply bounded_bounded_equiv. auto.
    - apply atmost_atmost_equiv. auto. }
  (* merges the two resulting quantifiers *)
  apply bounded_atmost_equiv. auto.
Qed.


End EquivalenceChain.
  
