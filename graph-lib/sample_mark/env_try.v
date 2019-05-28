Require Export VST.floyd.proofauto.
Require Export RamifyCoq.sample_mark.try.

Local Open Scope logic.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Global Existing Instance CompSpecs.
Global Existing Instance CS_legal.

Eval compute in (sizeof cenv_cs (Tstruct _T2 noattr)).

Print legal_alignas_type.
Print local_legal_alignas_type.

Definition node_type := (talignas 4%N (Tstruct _Node noattr)).
