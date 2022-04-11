section \<open>Constructs for Describing Communication\<close>

theory "Network_Equivalences-Communication"
  imports "Thorn_Calculus.Thorn_Calculus-Core_Bisimilarities"
begin

subsection \<open>Distributors\<close>

definition distributor :: "chan family \<Rightarrow> chan family list \<Rightarrow> process family" (infix \<open>\<Rightarrow>\<close> 52) where
  [simp]: "A \<Rightarrow> Bs = A \<triangleright>\<^sup>\<infinity> x. \<Prod>B \<leftarrow> Bs. B \<triangleleft> \<box> x"

lemma adapted_after_distributor:
  shows "(A \<Rightarrow> Bs) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<Rightarrow> map (\<lambda>B. B \<guillemotleft> \<E>) Bs"
  sorry

lemma distributor_idempotency [thorn_simps]:
  shows "A \<Rightarrow> Bs \<parallel> A \<Rightarrow> Bs \<sim>\<^sub>s A \<Rightarrow> Bs"
  unfolding distributor_def
  using repeated_receive_idempotency .

lemma distributor_nested_idempotency [thorn_simps]:
  shows "A \<Rightarrow> Bs \<parallel> (A \<Rightarrow> Bs \<parallel> P) \<sim>\<^sub>s A \<Rightarrow> Bs \<parallel> P"
  unfolding distributor_def
  using repeated_receive_nested_idempotency .

(*FIXME: Check whether we should add this lemma to \<^theory_text>\<open>thorn_simps\<close>. *)
lemma inner_distributor_redundancy:
  shows "A \<Rightarrow> Bs \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<Rightarrow> Bs \<parallel> \<P> x) \<sim>\<^sub>s A \<Rightarrow> Bs \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding distributor_def
  using inner_repeated_receive_redundancy .

subsection \<open>Loss Servers\<close>

definition loss :: "chan family \<Rightarrow> process family" (\<open>\<currency>\<^sup>?\<close>) where
  [simp]: "\<currency>\<^sup>? A = A \<Rightarrow> []"

lemma adapted_after_loss:
  shows "\<currency>\<^sup>? A \<guillemotleft> \<E> = \<currency>\<^sup>? (A \<guillemotleft> \<E>)"
  by (simp del: distributor_def add: adapted_after_distributor)

lemma loss_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>? A \<sim>\<^sub>s \<currency>\<^sup>? A"
  unfolding loss_def
  using distributor_idempotency .

lemma loss_nested_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>? A \<parallel> P) \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> P"
  unfolding loss_def
  using distributor_nested_idempotency .

lemma inner_loss_redundancy:
  shows "\<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>? A \<parallel> \<P> x) \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding loss_def
  using inner_distributor_redundancy .

subsection \<open>Duplication Servers\<close>

definition duplication :: "chan family \<Rightarrow> process family" (\<open>\<currency>\<^sup>+\<close>) where
  [simp]: "\<currency>\<^sup>+ A = A \<Rightarrow> [A, A]"

lemma adapted_after_duplication:
  shows "\<currency>\<^sup>+ A \<guillemotleft> \<E> = \<currency>\<^sup>+ (A \<guillemotleft> \<E>)"
  by (simp del: distributor_def add: adapted_after_distributor)

lemma duplication_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>+ A \<parallel> \<currency>\<^sup>+ A \<sim>\<^sub>s \<currency>\<^sup>+ A"
  unfolding duplication_def
  using distributor_idempotency .

lemma duplication_nested_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>+ A \<parallel> (\<currency>\<^sup>+ A \<parallel> P) \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> P"
  unfolding duplication_def
  using distributor_nested_idempotency .

lemma inner_duplication_redundancy:
  shows "\<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+ A \<parallel> \<P> x) \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding duplication_def
  using inner_distributor_redundancy .

lemma repeated_receive_split:
  assumes "\<And>x. \<P> x \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<zero>" and "\<And>x. \<Q> x \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<zero>"
  shows "\<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. (\<P> x \<parallel> \<Q> x) \<approx>\<^sub>s \<currency>\<^sup>+ A \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<Q> x"
  sorry

subsection \<open>Duploss Servers\<close>

definition duploss :: "chan family \<Rightarrow> process family" (\<open>\<currency>\<^sup>*\<close>) where
  [simp]: "\<currency>\<^sup>* A = \<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A"

lemma adapted_after_duploss:
  shows "\<currency>\<^sup>* A \<guillemotleft> \<E> = \<currency>\<^sup>* (A \<guillemotleft> \<E>)"
  by (simp only: duploss_def adapted_after_parallel adapted_after_loss adapted_after_duplication)

lemma duploss_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>* A \<parallel> \<currency>\<^sup>* A \<sim>\<^sub>s \<currency>\<^sup>* A"
  unfolding duploss_def
  using thorn_simps
  by equivalence

lemma duploss_nested_idempotency [thorn_simps]:
  shows "\<currency>\<^sup>* A \<parallel> (\<currency>\<^sup>* A \<parallel> P) \<sim>\<^sub>s \<currency>\<^sup>* A \<parallel> P"
  unfolding duploss_def
  using thorn_simps
  by equivalence

(*FIXME:
  Simplify the proof of the following lemma once #231 is resolved.

  In particular, do the following:

    \<^item> Turn the detailed proofs that involve
      \<^theory_text>\<open>repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity\<close> into single-step proofs
      that use the \<^theory_text>\<open>bisimilarity\<close> proof method.

    \<^item> Merge the resulting proofs with adjacent proofs if \<^theory_text>\<open>bisimilarity\<close> can solve the whole step.

    \<^item> Merge applications of \<^theory_text>\<open>parallel_commutativity\<close> and \<^theory_text>\<open>parallel_associativity\<close> when possible.

    \<^item> Get rid of applications of compatibility rules whenever \<^theory_text>\<open>bisimilarity\<close> can be used instead.
*)
lemma inner_duploss_redundancy:
  shows "\<currency>\<^sup>* A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>* A \<parallel> \<P> x) \<sim>\<^sub>s \<currency>\<^sup>* A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
proof -
  have "
    post_receive n X (\<lambda>x. (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    post_receive n X (\<lambda>x. \<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    for n and X
  proof -
    have "
      (\<lambda>e. (((\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> \<P> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. ((\<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel> \<P> (X e) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    also have "\<dots> = (\<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> \<currency>\<^sup>+ A \<guillemotleft> suffix n) \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e)"
      by (subst environment_dependent_parallel) (fact refl)
    also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> (\<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e))"
      using parallel_associativity .
    also have "\<dots> = (\<lambda>e. (\<currency>\<^sup>? A \<guillemotleft> suffix n \<parallel> (\<currency>\<^sup>+ A \<guillemotleft> suffix n \<parallel> \<P> (X e) \<guillemotleft> suffix n)) e)"
      by
        (subst (3) environment_dependent_parallel, subst (4) environment_dependent_parallel)
        (fact refl)
    also have "\<dots> = (\<lambda>e. ((\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> (X e))) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    finally show ?thesis
      unfolding post_receive_def .
  qed
  then have "
    (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> B \<triangleright>\<^sup>\<infinity> x. ((\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    by
      (intro
        parallel_is_right_compatible_with_synchronous_bisimilarity
        repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity
      )
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> (\<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> \<P> x)))"
    using thorn_simps
    by equivalence
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>+ A \<parallel> (\<currency>\<^sup>? A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    using inner_loss_redundancy
    by (rule parallel_is_right_compatible_with_synchronous_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+ A \<parallel> \<P> x))"
    using parallel_left_commutativity .
  also have "\<dots> \<sim>\<^sub>s \<currency>\<^sup>? A \<parallel> (\<currency>\<^sup>+ A \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x)"
    using inner_duplication_redundancy
    by (rule parallel_is_right_compatible_with_synchronous_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
    using parallel_associativity
    by equivalence
  finally show ?thesis
  unfolding duploss_def .
qed

lemma send_idempotency_under_duploss:
  shows "\<currency>\<^sup>* A \<parallel> A \<triangleleft> X \<parallel> A \<triangleleft> X \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> A \<triangleleft> X"
  sorry

subsection \<open>Unidirectional Bridges\<close>

definition
  unidirectional_bridge :: "chan family \<Rightarrow> chan family \<Rightarrow> process family"
  (infix \<open>\<rightarrow>\<close> 52)
where
  [simp]: "A \<rightarrow> B = A \<Rightarrow> [B]"

lemma adapted_after_unidirectional_bridge:
  shows "(A \<rightarrow> B) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<rightarrow> B \<guillemotleft> \<E>"
  by (simp del: distributor_def add: adapted_after_distributor)

lemma unidirectional_bridge_idempotency [thorn_simps]:
  shows "A \<rightarrow> B \<parallel> A \<rightarrow> B \<sim>\<^sub>s A \<rightarrow> B"
  unfolding unidirectional_bridge_def
  using distributor_idempotency .

lemma unidirectional_bridge_nested_idempotency [thorn_simps]:
  shows "A \<rightarrow> B \<parallel> (A \<rightarrow> B \<parallel> P) \<sim>\<^sub>s A \<rightarrow> B \<parallel> P"
  unfolding unidirectional_bridge_def
  using distributor_nested_idempotency .

lemma inner_unidirectional_bridge_redundancy:
  shows "A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<rightarrow> B \<parallel> \<P> x) \<sim>\<^sub>s A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
  unfolding unidirectional_bridge_def
  using inner_distributor_redundancy .

lemma repeated_receive_shortcut_redundancy:
  shows "A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<approx>\<^sub>s A \<rightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  sorry

lemma distributor_shortcut_redundancy:
  shows "A \<rightarrow> B \<parallel> B \<Rightarrow> Cs \<parallel> A \<Rightarrow> Cs \<approx>\<^sub>s A \<rightarrow> B \<parallel> B \<Rightarrow> Cs"
  unfolding distributor_def
  using repeated_receive_shortcut_redundancy .

lemma unidirectional_bridge_shortcut_redundancy:
  shows "A \<rightarrow> B \<parallel> B \<rightarrow> C \<parallel> A \<rightarrow> C \<approx>\<^sub>s A \<rightarrow> B \<parallel> B \<rightarrow> C"
  using distributor_shortcut_redundancy
  unfolding unidirectional_bridge_def .

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>* A \<parallel> A \<rightarrow> A \<approx>\<^sub>s \<currency>\<^sup>* A"
  sorry

lemma sidetrack_redundancy:
  shows "\<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> A \<Rightarrow> (B\<^sub>0 # Bs) \<parallel> A \<rightarrow> B\<^sub>0 \<approx>\<^sub>s \<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> A \<Rightarrow> (B\<^sub>0 # Bs)"
  sorry

lemma distributor_split:
  shows "\<currency>\<^sup>+ A \<parallel> \<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> A \<Rightarrow> Bs \<approx>\<^sub>s \<currency>\<^sup>+ A \<parallel> \<Prod>B \<leftarrow> Bs. \<currency>\<^sup>? B \<parallel> \<Prod>B \<leftarrow> Bs. A \<rightarrow> B"
  sorry

subsection \<open>Bidirectional Bridges\<close>

definition
  bidirectional_bridge :: "chan family \<Rightarrow> chan family \<Rightarrow> process family"
  (infix \<open>\<leftrightarrow>\<close> 52)
where
  [simp]: "A \<leftrightarrow> B = A \<rightarrow> B \<parallel> B \<rightarrow> A"

lemma adapted_after_bidirectional_bridge:
  shows "(A \<leftrightarrow> B) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<leftrightarrow> B \<guillemotleft> \<E>"
  by (simp only: bidirectional_bridge_def adapted_after_parallel adapted_after_unidirectional_bridge)

lemma bidirectional_bridge_idempotency [thorn_simps]:
  shows "A \<leftrightarrow> B \<parallel> A \<leftrightarrow> B \<sim>\<^sub>s A \<leftrightarrow> B"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma bidirectional_bridge_nested_idempotency [thorn_simps]:
  shows "A \<leftrightarrow> B \<parallel> (A \<leftrightarrow> B \<parallel> P) \<sim>\<^sub>s A \<leftrightarrow> B \<parallel> P"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma inner_bidirectional_bridge_redundancy:
  shows "A \<leftrightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<leftrightarrow> B \<parallel> \<P> x) \<sim>\<^sub>s A \<leftrightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
proof -
  have "
    post_receive n X (\<lambda>x. (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    post_receive n X (\<lambda>x. A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> x))"
    for n and X
  proof -
    have "
      (\<lambda>e. (((A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> \<P> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. (((A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (B \<rightarrow> A) \<guillemotleft> suffix n) \<parallel> \<P> (X e) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    also have "\<dots> = ((A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> (B \<rightarrow> A) \<guillemotleft> suffix n) \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e)"
      by (subst environment_dependent_parallel) (fact refl)
    also have "\<dots> \<sim>\<^sub>s (A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> ((B \<rightarrow> A) \<guillemotleft> suffix n \<parallel> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e))"
      using parallel_associativity .
    also have "\<dots> = (\<lambda>e. ((A \<rightarrow> B) \<guillemotleft> suffix n \<parallel> ((B \<rightarrow> A) \<guillemotleft> suffix n \<parallel> \<P> (X e) \<guillemotleft> suffix n)) e)"
      by
        (subst (3) environment_dependent_parallel, subst (4) environment_dependent_parallel)
        (fact refl)
    also have "\<dots> = (\<lambda>e. ((A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> (X e))) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    finally show ?thesis
      unfolding post_receive_def .
  qed
  then have "
    (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> C \<triangleright>\<^sup>\<infinity> x. ((A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> \<P> x)
    \<sim>\<^sub>s
    (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> x))"
    by
      (intro
        parallel_is_right_compatible_with_synchronous_bisimilarity
        repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity
      )
  also have "\<dots> \<sim>\<^sub>s B \<rightarrow> A \<parallel> (A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> \<P> x)))"
    using thorn_simps
    by equivalence
  also have "\<dots> \<sim>\<^sub>s B \<rightarrow> A \<parallel> (A \<rightarrow> B \<parallel> C \<triangleright>\<^sup>\<infinity> x. (B \<rightarrow> A \<parallel> \<P> x))"
    using inner_unidirectional_bridge_redundancy
    by (rule parallel_is_right_compatible_with_synchronous_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> C \<triangleright>\<^sup>\<infinity> x. (B \<rightarrow> A \<parallel> \<P> x))"
    using parallel_left_commutativity .
  also have "\<dots> \<sim>\<^sub>s A \<rightarrow> B \<parallel> (B \<rightarrow> A \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x)"
    using inner_unidirectional_bridge_redundancy
    by (rule parallel_is_right_compatible_with_synchronous_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s (A \<rightarrow> B \<parallel> B \<rightarrow> A) \<parallel> C \<triangleright>\<^sup>\<infinity> x. \<P> x"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding bidirectional_bridge_def .
qed

lemma bidirectional_bridge_commutativity [thorn_simps]:
  shows "A \<leftrightarrow> B \<sim>\<^sub>s B \<leftrightarrow> A"
  unfolding bidirectional_bridge_def
  using parallel_commutativity .

lemma forward_bridge_absorption:
  shows "A \<leftrightarrow> B \<parallel> A \<rightarrow> B \<sim>\<^sub>s A \<leftrightarrow> B"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma backward_bridge_absorption:
  shows "A \<leftrightarrow> B \<parallel> B \<rightarrow> A \<sim>\<^sub>s A \<leftrightarrow> B"
  unfolding bidirectional_bridge_def
  using thorn_simps
  by equivalence

lemma send_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<triangleleft> X \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleleft> X"
  sorry

lemma receive_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<triangleright> x. \<P> x \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleright> x. \<P> x"
  sorry

lemma general_parallel_channel_switch:
  assumes "\<And>x. fst x \<leftrightarrow> snd x \<parallel> \<P> (fst x) \<approx>\<^sub>s fst x \<leftrightarrow> snd x \<parallel> \<P> (snd x)"
  shows "\<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. \<P> (fst v) \<approx>\<^sub>s \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. \<P> (snd v)"
proof (induction vs)
  case Nil
  show ?case
    unfolding general_parallel.simps(1)
    by equivalence
next
  case (Cons v vs)
  have "
    (fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v) \<parallel> \<P> (fst v) \<parallel> \<Prod>x \<leftarrow> vs. \<P> (fst x)
    \<approx>\<^sub>s
    (fst v \<leftrightarrow> snd v \<parallel> \<P> (fst v)) \<parallel> (\<Prod>x \<leftarrow> vs. fst x \<leftrightarrow> snd x \<parallel> \<Prod>x \<leftarrow> vs. \<P> (fst x))"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s (fst v \<leftrightarrow> snd v \<parallel> \<P> (snd v)) \<parallel> (\<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. \<P> (snd v))"
    using assms and Cons.IH
    by (rule parallel_is_compatible_with_synchronous_weak_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s (fst v \<leftrightarrow> snd v \<parallel> \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v) \<parallel> (\<P> (snd v) \<parallel> \<Prod>v \<leftarrow> vs. \<P> (snd v))"
    using thorn_simps
    by equivalence
  finally show ?case
    unfolding general_parallel.simps(2) .
qed

lemma repeated_receive_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<triangleright>\<^sup>\<infinity> x. \<P> x"
  sorry

lemma distributor_source_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<Rightarrow> Cs \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<Rightarrow> Cs"
  unfolding distributor_def
  using repeated_receive_channel_switch .

(*FIXME:
  Simplify the proof of the following lemma once #231 is resolved.

  In particular, do the following:

    \<^item> Turn the detailed proofs that involve
      \<^theory_text>\<open>repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity\<close> into single-step proofs
      that use the \<^theory_text>\<open>bisimilarity\<close> proof method.

    \<^item> Merge the resulting proofs with adjacent proofs if \<^theory_text>\<open>bisimilarity\<close> can solve the whole step.

    \<^item> Merge applications of \<^theory_text>\<open>parallel_commutativity\<close> and \<^theory_text>\<open>parallel_associativity\<close> when possible.

    \<^item> Get rid of applications of compatibility rules whenever \<^theory_text>\<open>bisimilarity\<close> can be used instead.
*)
(*FIXME:
  The following proof uses \<^theory_text>\<open>general_parallel_conversion_deferral\<close> twice. Check whether this is
  unnecessary and, if yes, whether it should be avoided.
*)
lemma distributor_target_switch:
  shows
    "\<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> A \<Rightarrow> map fst vs \<approx>\<^sub>s \<Prod>v \<leftarrow> vs. fst v \<leftrightarrow> snd v \<parallel> A \<Rightarrow> map snd vs"
    (is "?\<P> vs \<parallel> _ \<approx>\<^sub>s ?\<P> vs \<parallel> _")
proof -
  \<comment> \<open>Specializations of lemmas:\<close>
  have inner_target_bridges_redundancy:
    "?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. (?\<P> vs \<parallel> \<Q> y) \<sim>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Q> y" for \<Q>
    using inner_bidirectional_bridge_redundancy
    by (rule inner_general_parallel_redundancy)
  have targets_switch:
    "?\<P> ws \<parallel> \<Prod>w \<leftarrow> ws. fst w \<triangleleft> Y \<approx>\<^sub>s ?\<P> ws \<parallel> \<Prod>w \<leftarrow> ws. snd w \<triangleleft> Y" for ws and Y
    using send_channel_switch
    by (rule general_parallel_channel_switch)
  have post_receive_targets_switch: "
    post_receive n X (\<lambda>x. ?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> x)
    \<approx>\<^sub>s
    post_receive n X (\<lambda>x. ?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> x)"
    for n and X
  proof -
    let ?ws = "map (\<lambda>v. (fst v \<guillemotleft> suffix n, snd v \<guillemotleft> suffix n)) vs"
    have "
      (\<lambda>e. ((?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. (\<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<triangleleft> \<box> (X e) \<guillemotleft> suffix n) e)"
      by
        (simp only:
          adapted_after_parallel
          adapted_after_general_parallel
          adapted_after_bidirectional_bridge
          adapted_after_send
        )
    also have "\<dots> = \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<triangleleft> X"
      by
        (
          subst environment_dependent_parallel,
          subst (2) environment_dependent_general_parallel,
          subst environment_dependent_send,
          transfer,
          simp only: comp_def constant_family_def
        )
    also have "\<dots> = \<Prod>w \<leftarrow> ?ws. fst w \<leftrightarrow> snd w \<parallel> \<Prod>w \<leftarrow> ?ws. fst w \<triangleleft> X"
      by (simp only: general_parallel_conversion_deferral fst_conv snd_conv)
    also have "\<dots> \<approx>\<^sub>s \<Prod>w \<leftarrow> ?ws. fst w \<leftrightarrow> snd w \<parallel> \<Prod>w \<leftarrow> ?ws. snd w \<triangleleft> X"
      using general_parallel_channel_switch [OF send_channel_switch] .
    also have "\<dots> = \<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. snd v \<guillemotleft> suffix n \<triangleleft> X"
      by (simp only: general_parallel_conversion_deferral fst_conv snd_conv)
    also have "\<dots> = (\<lambda>e. (\<Prod>v \<leftarrow> vs. fst v \<guillemotleft> suffix n \<leftrightarrow> snd v \<guillemotleft> suffix n \<parallel> \<Prod>v \<leftarrow> vs. snd v \<guillemotleft> suffix n \<triangleleft> \<box> (X e) \<guillemotleft> suffix n) e)"
      by
        (
          subst (2) environment_dependent_parallel,
          subst (4) environment_dependent_general_parallel,
          subst (2) environment_dependent_send,
          transfer,
          simp only: comp_def constant_family_def
        )
    also have "\<dots> = (\<lambda>e. ((?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> (X e)) \<guillemotleft> suffix n) e)"
      by
        (simp only:
          adapted_after_parallel
          adapted_after_general_parallel
          adapted_after_bidirectional_bridge
          adapted_after_send
        )
    finally show ?thesis
      unfolding post_receive_def .
  qed
  \<comment> \<open>The actual proof:\<close>
  have "?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> y \<approx>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. (?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. fst v \<triangleleft> \<box> y)"
    by
      (
        rule synchronous.bisimilarity_in_weak_bisimilarity [THEN predicate2D],
        rule synchronous.bisimilarity_symmetry_rule
      )
      (fact inner_target_bridges_redundancy)
  also have "\<dots> \<approx>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. (?\<P> vs \<parallel> \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> y)"
    by
      (intro
        parallel_is_right_compatible_with_synchronous_weak_bisimilarity
        repeated_receive_is_quasi_compatible_with_synchronous_weak_bisimilarity
      )
      (fact post_receive_targets_switch)
  also have "\<dots> \<approx>\<^sub>s ?\<P> vs \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Prod>v \<leftarrow> vs. snd v \<triangleleft> \<box> y"
    by
      (rule synchronous.bisimilarity_in_weak_bisimilarity [THEN predicate2D])
      (fact inner_target_bridges_redundancy)
  finally show ?thesis
    unfolding distributor_def and general_parallel_conversion_deferral .
qed

lemma loss_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? B"
  unfolding loss_def using distributor_source_switch .

lemma duplication_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ B"
proof -
  have "A \<leftrightarrow> B \<parallel> A \<Rightarrow> [A, A] \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<Rightarrow> [A, A]"
    using distributor_source_switch .
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> B \<Rightarrow> [A, A]"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow> [(A, B), (A, B)]. fst v \<leftrightarrow> snd v \<parallel> B \<Rightarrow> map fst [(A, B), (A, B)]"
    by simp
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow> [(A, B), (A, B)]. fst v \<leftrightarrow> snd v \<parallel> B \<Rightarrow> map snd [(A, B), (A, B)]"
    using distributor_target_switch .
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> B \<Rightarrow> [B, B]"
    by simp
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<Rightarrow> [B, B]"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding duplication_def .
qed

lemma duploss_channel_switch:
  shows "A \<leftrightarrow> B \<parallel> \<currency>\<^sup>* A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> \<currency>\<^sup>* B"
proof -
  have "A \<leftrightarrow> B \<parallel> (\<currency>\<^sup>? A \<parallel> \<currency>\<^sup>+ A) \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? A) \<parallel> \<currency>\<^sup>+ A"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>? B) \<parallel> \<currency>\<^sup>+ A"
    using loss_channel_switch
    by (rule parallel_is_left_compatible_with_synchronous_weak_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>? B \<parallel> (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ A)"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>? B \<parallel> (A \<leftrightarrow> B \<parallel> \<currency>\<^sup>+ B)"
    using duplication_channel_switch
    by (rule parallel_is_right_compatible_with_synchronous_weak_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> (\<currency>\<^sup>? B \<parallel> \<currency>\<^sup>+ B)"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding duploss_def .
qed

lemma unidirectional_bridge_source_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<rightarrow> C \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<rightarrow> C"
  unfolding unidirectional_bridge_def
  using distributor_source_switch .

lemma unidirectional_bridge_target_switch:
  shows "A \<leftrightarrow> B \<parallel> C \<rightarrow> A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<rightarrow> B"
proof -
  have "A \<leftrightarrow> B \<parallel> C \<Rightarrow> [A] \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> C \<Rightarrow> [A]"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow> [(A, B)]. fst v \<leftrightarrow> snd v \<parallel> C \<Rightarrow> map fst [(A, B)]"
    by simp
  also have "\<dots> \<approx>\<^sub>s \<Prod>v \<leftarrow>[(A, B)]. fst v \<leftrightarrow> snd v \<parallel> C \<Rightarrow> map snd [(A, B)]"
    using distributor_target_switch .
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> \<zero>) \<parallel> C \<Rightarrow> [B]"
    by simp
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<Rightarrow> [B]"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding unidirectional_bridge_def .
qed

lemma bidirectional_bridge_source_switch:
  shows "A \<leftrightarrow> B \<parallel> A \<leftrightarrow> C \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<leftrightarrow> C"
proof -
  have "A \<leftrightarrow> B \<parallel> (A \<rightarrow> C \<parallel> C \<rightarrow> A) \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> A \<rightarrow> C) \<parallel> C \<rightarrow> A"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s (A \<leftrightarrow> B \<parallel> B \<rightarrow> C) \<parallel> C \<rightarrow> A"
    using unidirectional_bridge_source_switch
    by (rule parallel_is_left_compatible_with_synchronous_weak_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s B \<rightarrow> C \<parallel> (A \<leftrightarrow> B \<parallel> C \<rightarrow> A)"
    using thorn_simps
    by equivalence
  also have "\<dots> \<approx>\<^sub>s B \<rightarrow> C \<parallel> (A \<leftrightarrow> B \<parallel> C \<rightarrow> B)"
    using unidirectional_bridge_target_switch
    by (rule parallel_is_right_compatible_with_synchronous_weak_bisimilarity)
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> (B \<rightarrow> C \<parallel> C \<rightarrow> B)"
    using thorn_simps
    by equivalence
  finally show ?thesis
    unfolding bidirectional_bridge_def .
qed

lemma bidirectional_bridge_target_switch:
  shows "A \<leftrightarrow> B \<parallel> C \<leftrightarrow> A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<leftrightarrow> B"
proof -
  have "A \<leftrightarrow> B \<parallel> C \<leftrightarrow> A \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> A \<leftrightarrow> C"
    using bidirectional_bridge_commutativity
    by equivalence
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> B \<leftrightarrow> C"
    using bidirectional_bridge_source_switch .
  also have "\<dots> \<approx>\<^sub>s A \<leftrightarrow> B \<parallel> C \<leftrightarrow> B"
    using bidirectional_bridge_commutativity
    by equivalence
  finally show ?thesis .
qed

lemma detour_squashing:
  shows "\<nu> b. (A \<leftrightarrow> \<box> b) \<approx>\<^sub>s A \<rightarrow> A"
  sorry

(*FIXME:
  Use \<^theory_text>\<open>equivalence\<close> and possible similar proof methods in the following proof once this is possible
  with higher operators like \<open>\<leftrightarrow>\<close>.
*)
lemma duploss_detour_collapse:
  shows "\<nu> b. (\<currency>\<^sup>* (\<box> b) \<parallel> A \<leftrightarrow> \<box> b) \<approx>\<^sub>s \<currency>\<^sup>* A"
proof -
  have "\<nu> b. (\<currency>\<^sup>* (\<box> b) \<parallel> A \<leftrightarrow> \<box> b) \<approx>\<^sub>s \<nu> b. (\<box> b \<leftrightarrow> A \<parallel> \<currency>\<^sup>* (\<box> b))"
    using thorn_simps
    sorry
  also have "\<dots> \<approx>\<^sub>s \<nu> b. (\<box> b \<leftrightarrow> A \<parallel> \<currency>\<^sup>* A)"
    using duploss_channel_switch
    sorry
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> \<nu> b. (A \<leftrightarrow> \<box> b)"
    using thorn_simps
    sorry
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>* A \<parallel> A \<rightarrow> A"
    using detour_squashing
    sorry
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>* A"
    using loop_redundancy_under_duploss
    by equivalence
  finally show ?thesis .
qed

end
