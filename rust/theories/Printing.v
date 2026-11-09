From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Utils Require Import MRString.

Record remapped_inductive := build_remapped_inductive {
  re_ind_name : string;
  re_ind_ctors : list string;
  (* The eliminator of a remapped [match]: [Some e] prints
     [e(branch1, ..., branchn, discr)].  When [e] ends with a comma, its own
     opening parenthesis and leading arguments are kept, so
     [Some "__nat_elim!(self,"] prints [__nat_elim!(self, branch1, ..., discr)];
     a [macro_rules!] eliminator gets [self] this way, which hygiene does not
     let its body name. *)
  re_ind_match : option string;
  }.

Record remaps := {
  remap_inductive : inductive -> option remapped_inductive;
  remap_constant : kername -> option string;
  remap_inline_constant : kername -> option string;
  }.

Definition no_remaps :=
  {| remap_inductive _ := None;
     remap_constant _ := None;
     remap_inline_constant _ := None |}.
