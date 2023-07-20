theory "Network_Equivalences-Diamond-Foundations"
  imports
    "Network_Equivalences-Communication"
begin

no_notation funcset (infixr \<open>\<rightarrow>\<close> 60)

abbreviation diamond_sending where
  "diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"

abbreviation diamond_receiving where
  "diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"

abbreviation initial_core where
  "initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>From link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>From link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<comment> \<open>From link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"

abbreviation transformed_core where
  "transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"

abbreviation cross_sending where
  "cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> m"

abbreviation cross_receiving where
  "cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> m \<rightarrow> r\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> m \<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> m \<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> m \<rightarrow> r\<^sub>3"

lemma focussing:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> c \<rightarrow> a \<approx>\<^sub>s a \<leftrightarrow> b \<parallel> a \<leftrightarrow> c" (is "?p \<approx>\<^sub>s ?q")
proof-
  have "?p \<approx>\<^sub>s
    (a \<rightarrow> b \<parallel> b \<rightarrow> c) \<parallel>
    (b \<rightarrow> c \<parallel> c \<rightarrow> a)"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    (a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c) \<parallel>
    (b \<rightarrow> c \<parallel> c \<rightarrow> a \<parallel> b \<rightarrow> a)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s
    a \<rightarrow> b \<parallel> c \<rightarrow> a \<parallel>
    (b \<rightarrow> a \<parallel> a \<rightarrow> c \<parallel> b \<rightarrow> c)"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    a \<rightarrow> b \<parallel> c \<rightarrow> a \<parallel>
    (b \<rightarrow> a \<parallel> a \<rightarrow> c)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s ?q"
    unfolding bidirectional_bridge_def using thorn_simps by equivalence
  finally show ?thesis .
qed

lemma core_transformation:
  shows "initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>s transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
proof -
  have "initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>s
    \<comment> \<open>Left triangle:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    \<comment> \<open>Right triangle:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0)"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<comment> \<open>Left triangle:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
    \<comment> \<open>Right triangle:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)"
    using focussing by equivalence
  also have "\<dots> \<approx>\<^sub>s transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    unfolding bidirectional_bridge_def using thorn_simps by equivalence
  finally show ?thesis .
qed

lemma sending_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>s ?q")
proof -
  have "?p \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<Parallel>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>0 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Parallel>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>1 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Parallel>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>2 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps
    using thorn_simps
    by (equivalence simplification: fst_conv snd_conv list.map)
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<Parallel>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>0 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Parallel>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>1 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Parallel>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>2 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    by (intro
      distributor_target_switch [THEN synchronous.weak.bisimilarity_symmetry_rule]
      synchronous.weak.bisimilarity_reflexivity_rule
      synchronous.weak.parallel_is_compatible_with_bisimilarity
    )
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps
    using thorn_simps
    by (equivalence simplification: fst_conv snd_conv list.map)
  also have "\<dots> \<approx>\<^sub>s
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x :: val. (l\<^sub>3\<^sub>0 \<triangleleft> \<box> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> \<box> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using thorn_simps sorry
    (* FIXME:
      This should by solvable by \<^theory_text>\<open>equivalence\<close> again once it is configured to reason under
      \<^theory_text>\<open>repeated_receive\<close>.
    *)
  also have "\<dots> \<approx>\<^sub>s
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x :: val. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> \<box> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> \<box> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x :: val. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> \<box> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using send_idempotency_under_duploss sorry
    (* FIXME:
      This should by solvable by \<^theory_text>\<open>equivalence\<close> again once it is configured to reason under
      \<^theory_text>\<open>repeated_receive\<close>.
    *)
  also have "\<dots> \<approx>\<^sub>s
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x :: val. l\<^sub>3\<^sub>0 \<triangleleft> \<box> x) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using thorn_simps sorry
    (* FIXME:
      This should by solvable by \<^theory_text>\<open>equivalence\<close> again once it is configured to reason under
      \<^theory_text>\<open>repeated_receive\<close>.
    *)
  also have "\<dots> \<approx>\<^sub>s ?q"
    unfolding unidirectional_bridge_def by equivalence
  finally show ?thesis .
qed

lemma receiving_collapse:
  shows "
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>s
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>s ?q")
proof -
  have "?p \<approx>\<^sub>s
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"
    using unidirectional_bridge_source_switch by equivalence
  also have "\<dots> \<approx>\<^sub>s ?q"
    using thorn_simps by equivalence
  finally show ?thesis .
qed

lemma core_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel>
      transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0"
proof -
  have "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel>
      transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Link 0--1:\<close> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> \<box> l\<^sub>0\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> \<box> l\<^sub>0\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> \<box> l\<^sub>1\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> \<box> l\<^sub>2\<^sub>3)"
    using thorn_simps sorry
    (* FIXME:
      This goal started to cause problems with the switch to the Þ-calculus. We hope that the
      \<^theory_text>\<open>iprover\<close>-based equivalence reasoner will be able to solve it.
    *)
  also have"\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    unfolding tagged_new_channel_def using duploss_detour_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    using thorn_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

end
