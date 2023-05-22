/// NSL.SecurityProperties (implementation)
/// ========================================
module NSL.SecurityProperties

// open NSL.Protocol
friend LabeledPKI
open LabeledRuntimeAPI
// open NSL.Sessions

let is_n_b_in_b_state a b idx_setstate v_b state_b idx_sess n_b =
  state_was_set_at idx_setstate b v_b state_b /\ 
  state_inv Sessions.nsl idx_setstate b v_b state_b /\ 
  idx_sess < Seq.length state_b /\
  (match Sessions.parse_session_st (state_b.[idx_sess]) with
  |Success (Sessions.ResponderSentMsg2 a' n_a n_b') -> n_b==n_b' /\ a = a'
  |Success (Sessions.ResponderReceivedMsg3 a' n_b') -> n_b==n_b' /\ a = a'
  |_ -> False
  )

let n_b_is_secret n_b = secrecy_lemma #(pki Sessions.nsl) n_b

let is_n_b_in_a_state a b idx_setstate v_a state_a idx_sess n_b =
  state_was_set_at idx_setstate a v_a state_a /\ 
  state_inv Sessions.nsl idx_setstate a v_a state_a /\ 
  idx_sess < Seq.length state_a /\
  (match Sessions.parse_session_st (state_a.[idx_sess]) with
  |Success (Sessions.InitiatorSentMsg3 b' n_a n_b') -> n_b==n_b' /\ b=b'
  |_ -> False
  )

let n_b_in_a_state_is_secret n_b = secrecy_lemma #(pki Sessions.nsl) n_b

let initiator_authentication i = ()

let responder_authentication i = ()

