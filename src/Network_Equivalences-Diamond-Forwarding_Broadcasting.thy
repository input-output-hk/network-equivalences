section \<open>Equivalence of a Diamond-Shaped Forwarding Network and a Cross-Shaped Broadcasting Network\<close>

theory "Network_Equivalences-Diamond-Forwarding_Broadcasting"
  imports "Network_Equivalences-Diamond-Foundations"
begin

abbreviation diamond_send_transfer where
  "diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> sb\<^sub>3"

abbreviation diamond_receive_transfer_and_forwarding where
  "diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel>
    \<comment> \<open>Node 2:\<close> rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel>
    \<comment> \<open>Node 3:\<close> rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3]"

abbreviation diamond where
  "diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
    )"

abbreviation buffer_sidetracks where
  "buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> rb\<^sub>3 \<rightarrow> sb\<^sub>3"

abbreviation cross where
  "cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>* (\<box> m) \<parallel>
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> m) \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> m)
    )"

lemma buffer_sidetrack_addition:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
    \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3"
    (is "?p \<approx>\<^sub>s ?q")
proof -
  have "?p \<approx>\<^sub>s
    \<comment> \<open>Node 0:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?a \<parallel> rb\<^sub>0 \<Rightarrow> [sb\<^sub>0, r\<^sub>0]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?a \<parallel> rb\<^sub>1 \<Rightarrow> [sb\<^sub>1, r\<^sub>1]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?a \<parallel> rb\<^sub>2 \<Rightarrow> [sb\<^sub>2, r\<^sub>2]) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?a \<parallel> rb\<^sub>3 \<Rightarrow> [sb\<^sub>3, r\<^sub>3])"
    unfolding general_parallel.simps and distributor_def using thorn_simps sorry
    (* FIXME:
      This should by solvable by \<^theory_text>\<open>equivalence\<close> again once it is configured to reason under
      \<^theory_text>\<open>repeated_receive\<close>.
    *)
  also have "\<dots> \<approx>\<^sub>s
    \<comment> \<open>Node 0:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?a \<parallel> rb\<^sub>0 \<Rightarrow> [sb\<^sub>0, r\<^sub>0] \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?a \<parallel> rb\<^sub>1 \<Rightarrow> [sb\<^sub>1, r\<^sub>1] \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?a \<parallel> rb\<^sub>2 \<Rightarrow> [sb\<^sub>2, r\<^sub>2] \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Parallel>a\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?a \<parallel> rb\<^sub>3 \<Rightarrow> [sb\<^sub>3, r\<^sub>3] \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3)"
    using sidetrack_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s ?q"
    unfolding general_parallel.simps and distributor_def using thorn_simps sorry
    (* FIXME:
      This should by solvable by \<^theory_text>\<open>equivalence\<close> again once it is configured to reason under
      \<^theory_text>\<open>repeated_receive\<close>.
    *)
  finally show ?thesis .
qed

lemma core_addition:
  shows "
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
    \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>s ?q")
proof -
  have "?p \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0)"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> sb\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3]) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> sb\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3]) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2])"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> sb\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3]) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> sb\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3]) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2])"
    using distributor_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0)"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>s
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    \<comment> \<open>Link 0--1:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>1\<^sub>3]. \<currency>\<^sup>?a \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3]) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>2\<^sub>3]. \<currency>\<^sup>?a \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3]) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (\<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (\<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?a \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2])"
    unfolding duploss_def and general_parallel.simps using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    \<comment> \<open>Link 0--1:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>1\<^sub>3]. \<currency>\<^sup>?a \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>1\<^sub>3]. l\<^sub>0\<^sub>1 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>2\<^sub>3]. \<currency>\<^sup>?a \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>2\<^sub>3]. l\<^sub>0\<^sub>2 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (\<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>3\<^sub>0]. l\<^sub>1\<^sub>3 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (\<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>3\<^sub>0]. l\<^sub>2\<^sub>3 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?a \<parallel> \<Parallel>a\<leftarrow>[l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. l\<^sub>3\<^sub>0 \<rightarrow> a)"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>s ?q"
    unfolding duploss_def and general_parallel.simps using thorn_simps by equivalence
  finally show ?thesis .
qed

lemma single_node_buffering_removal:
  shows "
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<nu> sb rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb] \<parallel> \<box> sb \<rightarrow> m \<parallel> m \<rightarrow> \<box> rb \<parallel> \<box> rb \<rightarrow> \<box> sb)
    \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
proof -
  have "
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb] \<parallel> \<box> sb \<rightarrow> m \<parallel> m \<rightarrow> \<box> rb \<parallel> \<box> rb \<rightarrow> \<box> sb)
    \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb] \<parallel> (m \<rightarrow> \<box> rb \<parallel> \<box> rb \<rightarrow> \<box> sb \<parallel> \<box> sb \<rightarrow> m))"
    using thorn_simps sorry
    (* FIXME:
      This goal started to cause problems with the switch to the Þ-calculus. We hope that the
      \<^theory_text>\<open>iprover\<close>-based equivalence reasoner will be able to solve it.

      On all following goals which proofs we had to temporarily replace by \<^theory_text>\<open>sorry\<close> we will not
      comment.
    *)
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb] \<parallel> (m \<leftrightarrow> \<box> rb \<parallel> m \<leftrightarrow> \<box> sb))"
    using focussing sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb] \<parallel> (m \<leftrightarrow> \<box> sb \<parallel> \<currency>\<^sup>?m) \<parallel> (m \<leftrightarrow> \<box> rb \<parallel> \<currency>\<^sup>+m))"
    unfolding duploss_def using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb] \<parallel> (m \<leftrightarrow> \<box> sb \<parallel> \<currency>\<^sup>? (\<box> sb)) \<parallel> (m \<leftrightarrow> \<box> rb \<parallel> \<currency>\<^sup>+ (\<box> rb)))"
    unfolding tagged_new_channel_def
    sorry
  also have "\<dots> \<approx>\<^sub>s
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> m \<leftrightarrow> \<box> sb \<parallel> m \<leftrightarrow> \<box> rb \<parallel> (\<currency>\<^sup>+ (\<box> rb) \<parallel> \<Parallel>a\<leftarrow>[r, \<box> sb]. \<currency>\<^sup>?a \<parallel> \<box> rb \<Rightarrow> [r, \<box> sb]))"
    unfolding general_parallel.simps using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> m \<leftrightarrow> \<box> sb \<parallel> m \<leftrightarrow> \<box> rb \<parallel> (\<currency>\<^sup>+ (\<box> rb) \<parallel> \<Parallel>a\<leftarrow>[r, \<box> sb]. \<currency>\<^sup>?a \<parallel> \<Parallel>a\<leftarrow>[r, \<box> sb]. \<box> rb \<rightarrow> a))"
    using distributor_split sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<rightarrow> r \<parallel> \<box> rb \<rightarrow> \<box> sb \<parallel> (\<box> sb \<leftrightarrow> m \<parallel> \<currency>\<^sup>? (\<box> sb)) \<parallel> (\<box> rb \<leftrightarrow> m \<parallel> \<currency>\<^sup>+ (\<box> rb)))"
    unfolding general_parallel.simps using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<rightarrow> r \<parallel> \<box> rb \<rightarrow> \<box> sb \<parallel> (\<box> sb \<leftrightarrow> m \<parallel> \<currency>\<^sup>?m) \<parallel> (\<box> rb \<leftrightarrow> m \<parallel> \<currency>\<^sup>+m))"
    unfolding tagged_new_channel_def
    sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<rightarrow> r \<parallel> \<box> sb \<leftrightarrow> m \<parallel> (\<box> rb \<leftrightarrow> m \<parallel> \<box> rb \<rightarrow> \<box> sb))"
    unfolding duploss_def using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<rightarrow> r \<parallel> \<box> sb \<leftrightarrow> m \<parallel> (\<box> rb \<leftrightarrow> m \<parallel> m \<rightarrow> \<box> sb))"
    unfolding tagged_new_channel_def
    sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<rightarrow> r \<parallel> \<box> rb \<leftrightarrow> m \<parallel> (\<box> sb \<leftrightarrow> m \<parallel> m \<rightarrow> \<box> sb))"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (s \<rightarrow> \<box> sb \<parallel> \<box> rb \<rightarrow> r \<parallel> \<box> rb \<leftrightarrow> m \<parallel> \<box> sb \<leftrightarrow> m)"
    using backward_bridge_absorption sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. ((\<box> sb \<leftrightarrow> m \<parallel> s \<rightarrow> \<box> sb) \<parallel> (\<box> rb \<leftrightarrow> m \<parallel> \<box> rb \<rightarrow> r))"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. ((\<box> sb \<leftrightarrow> m \<parallel> s \<rightarrow> m) \<parallel> (\<box> rb \<leftrightarrow> m \<parallel> m \<rightarrow> r))"
    unfolding tagged_new_channel_def
    sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> (\<langle>0\<rangle> \<nu> sb. m \<leftrightarrow> \<box> sb) \<parallel> (\<langle>1\<rangle> \<nu> rb. m \<leftrightarrow> \<box> rb)"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> m \<rightarrow> m \<parallel> m \<rightarrow> m"
    unfolding tagged_new_channel_def using detour_squashing by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> (\<currency>\<^sup>*m \<parallel> m \<rightarrow> m) \<parallel> (\<currency>\<^sup>*m \<parallel> m \<rightarrow> m)"
    using thorn_simps by equivalence
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> \<currency>\<^sup>*m \<parallel> \<currency>\<^sup>*m"
    using loop_redundancy_under_duploss by equivalence
  also have "\<dots> \<approx>\<^sub>s \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
    using thorn_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

theorem diamond_cross_equivalence:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3
    \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
proof -
  have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
    )
    \<approx>\<^sub>s
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3)
      )
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
        buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3)
      )
    )"
    using buffer_sidetrack_addition sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
        diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3)
      )
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
        \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
        diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
        initial_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
      )
    )"
    using core_addition sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      initial_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
    )"
    using core_transformation sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
        transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        diamond_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
      )
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
        transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        cross_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
      )
    )"
    using receiving_collapse sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      cross_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
        \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
        transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        diamond_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
      )
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      cross_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
        \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
        transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
        cross_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
      )
    )"
    using sending_collapse sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      cross_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      cross_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      (
        \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
        \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. (
          \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>1) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>0\<^sub>2) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>1\<^sub>3) \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>2\<^sub>3) \<parallel>
          transformed_core (\<box> l\<^sub>0\<^sub>1) (\<box> l\<^sub>0\<^sub>2) (\<box> l\<^sub>1\<^sub>3) (\<box> l\<^sub>2\<^sub>3) (\<box> l\<^sub>3\<^sub>0)
        )
      )
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      cross_sending (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      cross_receiving (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) (\<box> l\<^sub>3\<^sub>0) \<parallel>
      buffer_sidetracks (\<box> sb\<^sub>0) (\<box> sb\<^sub>1) (\<box> sb\<^sub>2) (\<box> sb\<^sub>3) (\<box> rb\<^sub>0) (\<box> rb\<^sub>1) (\<box> rb\<^sub>2) (\<box> rb\<^sub>3) \<parallel>
      \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0)
    )"
    unfolding tagged_new_channel_def using core_collapse sorry
  also have "\<dots> \<approx>\<^sub>s
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>4\<rangle> \<nu> rb\<^sub>0. (
          s\<^sub>0 \<rightarrow> \<box> sb\<^sub>0 \<parallel> \<box> rb\<^sub>0 \<Rightarrow> [r\<^sub>0, \<box> sb\<^sub>0] \<parallel> \<box> sb\<^sub>0 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> \<box> rb\<^sub>0 \<parallel> \<box> rb\<^sub>0 \<rightarrow> \<box> sb\<^sub>0
        )
      ) \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>5\<rangle> \<nu> rb\<^sub>1. (
          s\<^sub>1 \<rightarrow> \<box> sb\<^sub>1 \<parallel> \<box> rb\<^sub>1 \<Rightarrow> [r\<^sub>1, \<box> sb\<^sub>1] \<parallel> \<box> sb\<^sub>1 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> \<box> rb\<^sub>1 \<parallel> \<box> rb\<^sub>1 \<rightarrow> \<box> sb\<^sub>1
        )
      ) \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>6\<rangle> \<nu> rb\<^sub>2. (
          s\<^sub>2 \<rightarrow> \<box> sb\<^sub>2 \<parallel> \<box> rb\<^sub>2 \<Rightarrow> [r\<^sub>2, \<box> sb\<^sub>2] \<parallel> \<box> sb\<^sub>2 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> \<box> rb\<^sub>2 \<parallel> \<box> rb\<^sub>2 \<rightarrow> \<box> sb\<^sub>2
        )
      ) \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>7\<rangle> \<nu> rb\<^sub>3. (
          s\<^sub>3 \<rightarrow> \<box> sb\<^sub>3 \<parallel> \<box> rb\<^sub>3 \<Rightarrow> [r\<^sub>3, \<box> sb\<^sub>3] \<parallel> \<box> sb\<^sub>3 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> \<box> rb\<^sub>3 \<parallel> \<box> rb\<^sub>3 \<rightarrow> \<box> sb\<^sub>3
        )
      )
    )"
    using thorn_simps sorry
  also have "\<dots> \<approx>\<^sub>s
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      (\<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> s\<^sub>0 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0) \<parallel>
      (\<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> s\<^sub>1 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1) \<parallel>
      (\<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> s\<^sub>2 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2) \<parallel>
      (\<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel> s\<^sub>3 \<rightarrow> \<box> l\<^sub>3\<^sub>0 \<parallel> \<box> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3)
    )"
    unfolding tagged_new_channel_def using single_node_buffering_removal sorry
  also have "\<dots> \<approx>\<^sub>s
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>* (\<box> l\<^sub>3\<^sub>0) \<parallel>
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 (\<box> l\<^sub>3\<^sub>0) \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 (\<box> l\<^sub>3\<^sub>0)
    )"
    using thorn_simps sorry
  finally show ?thesis unfolding tagged_new_channel_def .
qed

end
