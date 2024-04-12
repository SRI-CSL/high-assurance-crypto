open EcList
open EcOption

open ACircuit

open AMPCProtocol
open ASecretSharing
open ACommitment

open ASigmaProtocol

module type ZKData = sig

  type witness_t
  type instance_t
  val relation : witness_t -> instance_t -> bool
                  
end

module MPCInTheHeadSigmaProtocolData
         (ZKD : ZKData)
         (SSD : sig include SecretSharingSchemeData with type secret_t = ZKD.witness_t end)
         (MPCD : sig include MPCProtocolData with type pid_t = SSD.pid_t and type pinput_t = ZKD.instance_t and type sinput_t = SSD.share_t and type output_t = bool end)
         (CSD : sig include CommitmentSchemeData with type msg_t = MPCD.view_t end)
         (RELC : sig val relc : MPCD.circuit_t end) = struct
  

  module SS = SecretSharingScheme (SSD)
  module MPC = MPCProtocol (MPCD)
  module CS = CommitmentScheme (CSD)

  type witness_t = ZKD.witness_t
  type instance_t = ZKD.instance_t
  let relation = ZKD.relation

  type prover_input_t = witness_t * instance_t
  type verifier_input_t = instance_t
  type inputs_t = prover_input_t * verifier_input_t

  type prover_rand_t = SS.rand_t * MPC.rands_t * (SS.pid_t * CS.rand_t) list
  type verifier_rand_t = SSD.pid_t * SSD.pid_t
  type rands_t = prover_rand_t * verifier_rand_t

  type prover_output_t = unit
  type verifier_output_t = bool
  type outputs_t = prover_output_t * verifier_output_t

  type committed_view_t = MPC.view_t * CS.commit_info_t
  type committed_views_t = (SS.pid_t * committed_view_t) list

  let get_committed_view (pid : SS.pid_t) (cvs : committed_views_t) : committed_view_t = oget (assoc cvs pid)

  type commitment_t = (SS.pid_t * CS.commitment_t) list

  let get_party_commitment (pid : SS.pid_t) (cv : commitment_t) : CS.commitment_t = oget (assoc cv pid)

  type challenge_t = SSD.pid_t * SSD.pid_t
  type response_t = (MPC.view_t * CS.opening_string_t) * 
                    (MPC.view_t * CS.opening_string_t)

  type prover_state_t = committed_views_t
  type verifier_state_t = instance_t * commitment_t * challenge_t

  let relc : MPC.circuit_t = RELC.relc
                        
  let commitment (rp : prover_rand_t) (xp : prover_input_t) : prover_state_t * commitment_t =
    
    let (w,x) = xp in
    
    let (r_ss, r_mpc, r_cs) = rp in

    let ws = SS.share r_ss w in
    
    let x_mpc = map (fun pid -> (pid, (x, oget (assoc ws pid)))) SS.pid_set in
    
    let (tr,y) = MPC.protocol relc r_mpc x_mpc in
    
    let vs = map (fun pid -> (pid, (oget (assoc x_mpc pid), oget (assoc r_mpc pid), oget (assoc tr pid)))) SS.pid_set in
    
    let cvs = map (fun pid -> 
                    let r_c = oget (assoc r_cs pid) in
                    let v = oget (assoc vs pid) in 
                    (pid, (v, CS.commit r_c v))) SS.pid_set in

    let cs = map (fun pid -> (pid, fst (snd (oget (assoc cvs pid))))) SS.pid_set in
    
    (cvs, cs)

  let challenge (rv : verifier_rand_t) (xv : verifier_input_t) (c : commitment_t) : verifier_state_t * challenge_t =
    let ch = ((xv,c,rv),rv) in
    ch

  let get_party_committed_view (pid : SSD.pid_t) (cv : committed_views_t) : committed_view_t = oget (assoc cv pid)

  let response (stp : prover_state_t) (ch : challenge_t) : response_t =

    let cvs = stp in
    let (i,j) = ch in
    
    let cvi = get_party_committed_view i cvs in
    let (vi, cii) = cvi in
    let cvj = get_party_committed_view j cvs in
    let (vj, cij) = cvj in

    ((vi, snd cii), (vj, snd cij))

  let check (stv : verifier_state_t) (r : response_t) : bool =

    let (xv, cs, rv) = stv in
    let (i,j) = rv in

    let (vosi, vosj) = r in
    let (vi, osi) = vosi in
    let (vj, osj) = vosj in
    
    let (xi,ri,tri) = vi in
    let (xj,rj,trj) = vj in
    
    let ci = get_party_commitment i cs in
    let cj = get_party_commitment j cs in

    CS.verify vi (ci,osi) && CS.verify vj (cj,osj) &&
              MPC.consistent_views relc xv vi vj i j &&
                MPC.local_output relc i vi && MPC.local_output relc j vj
    
  type trace_t = commitment_t * challenge_t * response_t

end

module MPCInTheHead (ZKD : ZKData)
         (SSD : sig include SecretSharingSchemeData with type secret_t = ZKD.witness_t end)
         (MPCD : sig include MPCProtocolData with type pid_t = SSD.pid_t and type pinput_t = ZKD.instance_t and type sinput_t = SSD.share_t and type output_t = bool end)
         (CSD : sig include CommitmentSchemeData with type msg_t = MPCD.view_t end)
         (RELC : sig val relc : MPCD.circuit_t end) = ZKSigmaProtocol (MPCInTheHeadSigmaProtocolData (ZKD) (SSD) (MPCD) (CSD) (RELC))
