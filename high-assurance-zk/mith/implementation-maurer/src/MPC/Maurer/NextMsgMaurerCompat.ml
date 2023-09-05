open NextMsgECPervasive
open NextMsgECLogic
open NextMsgECList
open NextMsgECInt
open NextMsgECCore
open NextMsgMaurerP
open NextMsgMaurerAPI
open NextMsgMaurerProtocol
module MaurerDomain = struct
    type wire_t = NextMsgMaurerAPI.MaurerAPI._val
    let wire_to_bool (w : wire_t) : Pervasive.bool =
                                                       (Pervasive.eq w (NextMsgMaurerAPI.MaurerAPI.zero_val))
end
module MaurerProtocolFunctionality = struct
    type pinput_tt = (NextMsgMaurerAPI.MaurerAPI._val) List.list
    type sinput_tt = (NextMsgMaurerAPI.MaurerAPI.shr) List.list
    type input_tt = (pinput_tt * sinput_tt)
    type inputs_tt = ((Pervasive.int * input_tt)) List.list
    type sinputs_tt = ((Pervasive.int * sinput_tt)) List.list
    type outputs_tt = ((Pervasive.int * NextMsgMaurerAPI.MaurerAPI._val)) List.list
    let from_input_t (i : NextMsgMaurerAPI.MaurerAPI.pid) (x : input_tt) : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) =
                                                                                                                                            (let (pubs) = (List.map (NextMsgMaurerAPI.MaurerAPI.party_pshare i) (fst x)) in
                                                                                                                                             (let (secs) = (snd x) in
                                                                                                                                              (let (shrs) = (AuxList.cat pubs secs) in
                                                                                                                                               (let (wst) = (NextMsgMaurerAPI.MaurerAPI.mkwire_st i (List.size shrs) (NextMsgIMap.IMap.ofset (fun (wid : Pervasive.int) -> (List.nth (Pervasive.witness) shrs wid)) (NextMsgISet.ISet.iset (List.size shrs)))) in
                                                                                                                                                (let (pst) = (NextMsgISet.ISet.iset (List.size pubs)) in
                                                                                                                                                 (wst , pst))))))
    let from_inputs_t (xs : inputs_tt) : ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset))))) =
                                                                                                                                                                                                                                                                                                                                                                              (NextMsgMaurerP.MaurerP.init (fun (i : Pervasive.int) -> (from_input_t i (Logic.oget (List.assoc xs i)))))
    let to_pinput_t (xs : MaurerGate.share) : (NextMsgMaurerAPI.MaurerAPI._val) List.list =
                                                                                              (let (npubs) = (NextMsgISet.ISet.card (snd xs)) in
                                                                                               (List.map (fun (k : NextMsgMaurerAPI.MaurerAPI.wid) -> (NextMsgMaurerAPI.MaurerAPI.party_unpshare (NextMsgMaurerAPI.MaurerAPI.get_wire_st_shr (fst xs) k))) (AuxList.iseq npubs)))
    let to_sinput_t (xs : MaurerGate.share) : (NextMsgMaurerAPI.MaurerAPI.shr) List.list =
                                                                                             (let (npubs) = (NextMsgISet.ISet.card (snd xs)) in
                                                                                              (let (nsecs) = (Int.minus (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst xs)) npubs) in
                                                                                               (List.map (fun (k : Pervasive.int) -> (NextMsgMaurerAPI.MaurerAPI.get_wire_st_shr (fst xs) (Int.plus npubs k))) (AuxList.iseq nsecs))))
    let to_input_t (xs : MaurerGate.share) : ((NextMsgMaurerAPI.MaurerAPI._val) List.list * (NextMsgMaurerAPI.MaurerAPI.shr) List.list) =
                                                                                                                                            ((to_pinput_t xs) , (to_sinput_t xs))
    let to_sinputs_t (xs : (MaurerGate.share) NextMsgMaurerP.MaurerP.arrayN) : ((Pervasive.int * (NextMsgMaurerAPI.MaurerAPI.shr) List.list)) List.list =
                                                                                                                                                            (List.map (fun (i : Pervasive.int) -> (i , (to_sinput_t (NextMsgMaurerP.MaurerP.get xs i)))) (AuxList.iseq (Pervasive.mk_int 5)))
    let to_outputs_t (o : NextMsgMaurerAPI.MaurerAPI._val) : ((Pervasive.int * NextMsgMaurerAPI.MaurerAPI._val)) List.list =
                                                                                                                               (List.map (fun (i : Pervasive.int) -> (i , o)) (AuxList.iseq (Pervasive.mk_int 5)))
    let from_outputs_t (o : outputs_tt) : NextMsgMaurerAPI.MaurerAPI._val =
                                                                              (snd (List.head (Pervasive.witness) o))
    type circuit_tt = (MaurerCircuit.circuit * (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgISet.ISet.iset))
    let consistent_inputs (c : circuit_tt) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (wi : MaurerGate.share) (wj : MaurerGate.share) : Pervasive.bool =
                                                                                                                                                                                          (Pervasive._and (Pervasive.eq (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst wi)) (Aux.snd3 c)) (Pervasive._and (Pervasive.eq (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst wj)) (Aux.snd3 c)) (Pervasive._and (NextMsgISet.ISet.equal (snd wi) (Aux.thr3 c)) (Pervasive._and (NextMsgISet.ISet.equal (snd wj) (Aux.thr3 c)) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.g_valid_share wi) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.g_valid_share wj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j wi wj)))))))
    let valid_inputs' (c : circuit_tt) (ws : (MaurerGate.share) Aux.array5) : Pervasive.bool =
                                                                                                 (List.all (fun (i : Pervasive.int) -> (List.all (fun (j : Pervasive.int) -> (consistent_inputs c i j (NextMsgMaurerP.MaurerP.get ws i) (NextMsgMaurerP.MaurerP.get ws j))) (AuxList.iseq (Pervasive.mk_int 5)))) (AuxList.iseq (Pervasive.mk_int 5)))
    type circuit_t = (MaurerCircuit.circuit * (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgISet.ISet.iset))
    let n : Pervasive.int =
                              (Pervasive.mk_int 5)
    let t : Pervasive.int =
                              (Pervasive.mk_int 2)
    type pid_t = Pervasive.int
    let pid_set : (Pervasive.int) List.list =
                                                (AuxList.iseq (Pervasive.mk_int 5))
    type pinput_t = (NextMsgMaurerAPI.MaurerAPI._val) List.list
    type sinput_t = (NextMsgMaurerAPI.MaurerAPI.shr) List.list
    type input_t = (pinput_t * sinput_t)
    type inputs_t = ((pid_t * input_t)) List.list
    type pinputs_t = ((pid_t * pinput_t)) List.list
    type sinputs_t = ((pid_t * sinput_t)) List.list
    let input (pid : pid_t) (xs : inputs_t) : input_t =
                                                          (Logic.oget (List.assoc xs pid))
    let pinput (pid : pid_t) (xs : inputs_t) : pinput_t =
                                                            (fst (input pid xs))
    let sinput (pid : pid_t) (xs : inputs_t) : sinput_t =
                                                            (snd (input pid xs))
    let mk_inputs (xp : pinput_t) (sx : ((pid_t * sinput_t)) List.list) : ((pid_t * (pinput_t * sinput_t))) List.list =
                                                                                                                          (List.map (fun (pid : pid_t) -> (pid , (xp , (Logic.oget (List.assoc sx pid))))) (pid_set))
    let pinputs (xs : inputs_t) : ((pid_t * pinput_t)) List.list =
                                                                     (List.map (fun (pid : pid_t) -> (pid , (fst (Logic.oget (List.assoc xs pid))))) (pid_set))
    let sinputs (xs : inputs_t) : ((pid_t * sinput_t)) List.list =
                                                                     (List.map (fun (pid : pid_t) -> (pid , (snd (Logic.oget (List.assoc xs pid))))) (pid_set))
    let rec valid_circuit (c : circuit_t) : Pervasive.bool =
                                                               (MaurerCircuit.valid_circuit (Aux.fst3 c) (Aux.snd3 c) (Aux.thr3 c))
    let valid_inputs (c : circuit_t) (xs : inputs_t) : Pervasive.bool =
                                                                          (Pervasive._and (Pervasive.eq (List.unzip1 xs) (pid_set)) (valid_inputs' c (from_inputs_t xs)))
    type output_t = NextMsgMaurerAPI.MaurerAPI._val
    type outputs_t = ((pid_t * output_t)) List.list
    let output (pid : pid_t) (xs : outputs_t) : output_t =
                                                             (Logic.oget (List.assoc xs pid))
    let to_inputs_t (xp : pinput_t) (xs : (MaurerGate.share) NextMsgMaurerP.MaurerP.arrayN) : ((pid_t * (pinput_t * sinput_t))) List.list =
                                                                                                                                              (mk_inputs xp (to_sinputs_t xs))
end
module MaurerProtocol = struct
    type poutput_tt = Pervasive.unit
    type poutputs_tt = ((MaurerProtocolFunctionality.pid_t * poutput_tt)) List.list
    type in_messages_tt = MaurerReveal.ST.in_msgs
    type trace_tt = (poutputs_tt * in_messages_tt)
    type traces_tt = ((MaurerProtocolFunctionality.pid_t * trace_tt)) List.list
    type rand_tt = (MaurerGate.GT.local_rand) List.list
    type rands_tt = ((MaurerProtocolFunctionality.pid_t * rand_tt)) List.list
    type view_tt = (MaurerProtocolFunctionality.input_t * (rand_tt * trace_tt))
    type views_tt = ((MaurerProtocolFunctionality.pid_t * view_tt)) List.list
    let to_rands_t (rs : (MaurerReveal.ST.local_rand) NextMsgMaurerP.MaurerP.arrayN) : ((Pervasive.int * MaurerReveal.ST.local_rand)) List.list =
                                                                                                                                                    (NextMsgMaurerP.MaurerP.to_assoc rs)
    let from_rands_t (rs : rands_tt) : (rand_tt * (rand_tt * (rand_tt * (rand_tt * rand_tt)))) =
                                                                                                   (NextMsgMaurerP.MaurerP.init (fun (i : MaurerProtocolFunctionality.pid_t) -> (Logic.oget (List.assoc rs i))))
    let to_view_t (v : MaurerReveal.ST.view) : (((NextMsgMaurerAPI.MaurerAPI._val) List.list * (NextMsgMaurerAPI.MaurerAPI.shr) List.list) * (MaurerReveal.ST.local_rand * (((Pervasive.int * Pervasive.unit)) List.list * MaurerReveal.ST.in_msgs))) =
                                                                                                                                                                                                                                                          (let (pouts) = (List.map (fun (i : Pervasive.int) -> (i , (Pervasive.tt))) (MaurerProtocolFunctionality.pid_set)) in
                                                                                                                                                                                                                                                           ((MaurerProtocolFunctionality.to_input_t (Aux.fst3 v)) , ((Aux.thr3 v) , (pouts , (Aux.snd3 v)))))
    let from_view_t (i : NextMsgMaurerAPI.MaurerAPI.pid) (v : view_tt) : ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (in_messages_tt * rand_tt)) =
                                                                                                                                                                         ((MaurerProtocolFunctionality.from_input_t i (Aux.fst3 v)) , ((Aux.thr3 (snd v)) , (Aux.snd3 v)))
    let from_views_t (vs : views_tt) : (((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (in_messages_tt * rand_tt)) * (((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (in_messages_tt * rand_tt)) * (((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (in_messages_tt * rand_tt)) * (((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (in_messages_tt * rand_tt)) * ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) * (in_messages_tt * rand_tt)))))) =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (NextMsgMaurerP.MaurerP.init (fun (i : MaurerProtocolFunctionality.pid_t) -> (from_view_t i (Logic.oget (List.assoc vs i)))))
    let to_traces_t (msgs : (MaurerReveal.ST.in_msgs) NextMsgMaurerP.MaurerP.arrayN) : ((Pervasive.int * (((Pervasive.int * Pervasive.unit)) List.list * MaurerReveal.ST.in_msgs))) List.list =
                                                                                                                                                                                                  (let (pouts) = (List.map (fun (i : Pervasive.int) -> (i , (Pervasive.tt))) (MaurerProtocolFunctionality.pid_set)) in
                                                                                                                                                                                                   (List.map (fun (i : Pervasive.int) -> (i , (pouts , (NextMsgMaurerP.MaurerP.get msgs i)))) (MaurerProtocolFunctionality.pid_set)))
    let to_outputs_t' (o : (MaurerReveal.ST.local_output) NextMsgMaurerP.MaurerP.arrayN) : ((Pervasive.int * MaurerReveal.ST.local_output)) List.list =
                                                                                                                                                          (List.map (fun (i : Pervasive.int) -> (i , (NextMsgMaurerP.MaurerP.get o i))) (MaurerProtocolFunctionality.pid_set))
    let valid_view_t (_ : MaurerProtocolFunctionality.pid_t) (v : view_tt) : Pervasive.bool =
                                                                                                (Pervasive.eq (Aux.snd3 (snd v)) (List.map (fun (i0 : Pervasive.int) -> (i0 , (Pervasive.tt))) (MaurerProtocolFunctionality.pid_set)))
    let consistent_rands' (x : (MaurerCircuit.G._Gate) List.list) (ri : MaurerCircuit.CT.local_rand) (rj : MaurerCircuit.CT.local_rand) : Pervasive.bool =
                                                                                                                                                             (Pervasive._and (MaurerCircuit.circ_valid_rand x ri) (MaurerCircuit.circ_valid_rand x rj))
    let consistent_views' (x : MaurerProtocolFunctionality.circuit_t) (i : Pervasive.int) (j : Pervasive.int) (vi : MaurerReveal.ST.view) (vj : MaurerReveal.ST.view) : Pervasive.bool =
                                                                                                                                                                                           (Pervasive._and (MaurerReveal.ST.valid_view (Aux.fst3 x) vi) (Pervasive._and (MaurerReveal.ST.valid_view (Aux.fst3 x) vj) (Pervasive._and (MaurerReveal.ST.eq_rmsgs (MaurerReveal.get_view_in_msgs j vi) (MaurerReveal.get_view_out_msgs j i (Aux.fst3 x) vj)) (Pervasive._and (MaurerReveal.ST.eq_rmsgs (MaurerReveal.get_view_in_msgs i vj) (MaurerReveal.get_view_out_msgs i j (Aux.fst3 x) vi)) (Pervasive._and (MaurerProtocolFunctionality.consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands' (Aux.fst3 x) (Aux.thr3 vi) (Aux.thr3 vj)))))))
    module ProtocolFunctionality = struct
        type circuit_t = MaurerProtocolFunctionality.circuit_t
        let rec n : Pervasive.int =
                                      (MaurerProtocolFunctionality.n)
        let rec t : Pervasive.int =
                                      (MaurerProtocolFunctionality.t)
        type pid_t = MaurerProtocolFunctionality.pid_t
        let rec pid_set : (Pervasive.int) List.list =
                                                        (MaurerProtocolFunctionality.pid_set)
        type pinput_t = MaurerProtocolFunctionality.pinput_t
        type sinput_t = MaurerProtocolFunctionality.sinput_t
        type input_t = MaurerProtocolFunctionality.input_t
        type inputs_t = MaurerProtocolFunctionality.inputs_t
        type pinputs_t = MaurerProtocolFunctionality.pinputs_t
        type sinputs_t = MaurerProtocolFunctionality.sinputs_t
        let rec input : (MaurerProtocolFunctionality.pid_t -> (MaurerProtocolFunctionality.inputs_t -> MaurerProtocolFunctionality.input_t)) =
                                                                                                                                                 (MaurerProtocolFunctionality.input)
        let rec pinput : (MaurerProtocolFunctionality.pid_t -> (MaurerProtocolFunctionality.inputs_t -> MaurerProtocolFunctionality.pinput_t)) =
                                                                                                                                                   (MaurerProtocolFunctionality.pinput)
        let rec sinput : (MaurerProtocolFunctionality.pid_t -> (MaurerProtocolFunctionality.inputs_t -> MaurerProtocolFunctionality.sinput_t)) =
                                                                                                                                                   (MaurerProtocolFunctionality.sinput)
        let rec mk_inputs : (MaurerProtocolFunctionality.pinput_t -> (((MaurerProtocolFunctionality.pid_t * MaurerProtocolFunctionality.sinput_t)) List.list -> ((MaurerProtocolFunctionality.pid_t * (MaurerProtocolFunctionality.pinput_t * MaurerProtocolFunctionality.sinput_t))) List.list)) =
                                                                                                                                                                                                                                                                                                      (MaurerProtocolFunctionality.mk_inputs)
        let rec pinputs : (MaurerProtocolFunctionality.inputs_t -> ((MaurerProtocolFunctionality.pid_t * MaurerProtocolFunctionality.pinput_t)) List.list) =
                                                                                                                                                               (MaurerProtocolFunctionality.pinputs)
        let rec sinputs : (MaurerProtocolFunctionality.inputs_t -> ((MaurerProtocolFunctionality.pid_t * MaurerProtocolFunctionality.sinput_t)) List.list) =
                                                                                                                                                               (MaurerProtocolFunctionality.sinputs)
        let rec valid_circuit : (MaurerProtocolFunctionality.circuit_t -> Pervasive.bool) =
                                                                                              (MaurerProtocolFunctionality.valid_circuit)
        let rec valid_inputs : (MaurerProtocolFunctionality.circuit_t -> (MaurerProtocolFunctionality.inputs_t -> Pervasive.bool)) =
                                                                                                                                       (MaurerProtocolFunctionality.valid_inputs)
        type output_t = MaurerProtocolFunctionality.output_t
        type outputs_t = MaurerProtocolFunctionality.outputs_t
        let rec output : (MaurerProtocolFunctionality.pid_t -> (MaurerProtocolFunctionality.outputs_t -> MaurerProtocolFunctionality.output_t)) =
                                                                                                                                                    (MaurerProtocolFunctionality.output)
    end
    type rand_t = (MaurerGate.GT.local_rand) List.list
    type rands_t = ((ProtocolFunctionality.pid_t * rand_t)) List.list
    let rand (pid : ProtocolFunctionality.pid_t) (rs : rands_t) : rand_t =
                                                                             (Logic.oget (List.assoc rs pid))
    let valid_rand (c : ProtocolFunctionality.circuit_t) (r : rand_t) : Pervasive.bool =
                                                                                           (MaurerCircuit.circ_valid_rand (Aux.fst3 c) r)
    let valid_rands (c : ProtocolFunctionality.circuit_t) (rs : rands_t) : Pervasive.bool =
                                                                                              (Pervasive._and (Pervasive.eq (List.unzip1 rs) (ProtocolFunctionality.pid_set)) (assert false))
    type in_messages_t = MaurerReveal.ST.in_msgs
    type poutput_t = Pervasive.unit
    type poutputs_t = ((ProtocolFunctionality.pid_t * poutput_t)) List.list
    let poutput (pid : ProtocolFunctionality.pid_t) (pouts : poutputs_t) : poutput_t =
                                                                                         (Logic.oget (List.assoc pouts pid))
    type trace_t = (poutputs_t * in_messages_t)
    type traces_t = ((ProtocolFunctionality.pid_t * trace_t)) List.list
    let trace (pid : ProtocolFunctionality.pid_t) (trs : traces_t) : trace_t =
                                                                                 (Logic.oget (List.assoc trs pid))
    type view_t = (ProtocolFunctionality.input_t * (rand_t * trace_t))
    type views_t = ((ProtocolFunctionality.pid_t * view_t)) List.list
    let view (pid : ProtocolFunctionality.pid_t) (vs : views_t) : view_t =
                                                                             (Logic.oget (List.assoc vs pid))
    let local_output (c : ProtocolFunctionality.circuit_t) (i : NextMsgMaurerAPI.MaurerAPI.pid) (v : view_t) : MaurerReveal.ST.local_output =
                                                                                                                                                (let (vi) = (from_view_t i v) in
                                                                                                                                                 (snd (MaurerReveal.local_protocol i (Aux.fst3 c) vi)))
    let protocol (c : ProtocolFunctionality.circuit_t) (rs : rands_t) (ws : ProtocolFunctionality.inputs_t) : (((Pervasive.int * (((Pervasive.int * Pervasive.unit)) List.list * MaurerReveal.ST.in_msgs))) List.list * ((Pervasive.int * MaurerReveal.ST.local_output)) List.list) =
                                                                                                                                                                                                                                                                                        (let (ws') = (MaurerProtocolFunctionality.from_inputs_t ws) in
                                                                                                                                                                                                                                                                                         (let (rs') = (from_rands_t rs) in
                                                                                                                                                                                                                                                                                          (let (to') = (MaurerReveal.stateful_protocol (Aux.fst3 c) ws' rs') in
                                                                                                                                                                                                                                                                                           (let (t) = (to_traces_t (NextMsgMaurerP.MaurerP.map (fun (x : (MaurerReveal.ST.local_input * (MaurerReveal.ST.in_msgs * MaurerReveal.ST.local_rand))) -> (Aux.snd3 x)) (Aux.fst3 to'))) in
                                                                                                                                                                                                                                                                                            (let (o) = (to_outputs_t' (snd to')) in
                                                                                                                                                                                                                                                                                             (t , o))))))
    let consistent_views (c : ProtocolFunctionality.circuit_t) (vi : view_t) (vj : view_t) (i : ProtocolFunctionality.pid_t) (j : ProtocolFunctionality.pid_t) : Pervasive.bool =
                                                                                                                                                                                    (let (vi') = (from_view_t i vi) in
                                                                                                                                                                                     (let (vj') = (from_view_t j vj) in
                                                                                                                                                                                      (Pervasive._and (valid_view_t i vi) (Pervasive._and (valid_view_t j vi) (consistent_views' c i j vi' vj')))))
    let consistent_views_public (c : ProtocolFunctionality.circuit_t) (xp : ProtocolFunctionality.pinput_t) (vi : view_t) (vj : view_t) (i : ProtocolFunctionality.pid_t) (j : ProtocolFunctionality.pid_t) : Pervasive.bool =
                                                                                                                                                                                                                                 (Pervasive._and (Pervasive.eq (fst (Aux.fst3 vi)) xp) (Pervasive._and (Pervasive.eq (fst (Aux.fst3 vj)) xp) (consistent_views c vi vj i j)))
    let consistent_trace_public (c : ProtocolFunctionality.circuit_t) (xp : ProtocolFunctionality.pinput_t) (vs : ((ProtocolFunctionality.pid_t * view_t)) List.list) : Pervasive.bool =
                                                                                                                                                                                           (assert false)
    let extract_inputs (xs : ProtocolFunctionality.inputs_t) (pids : (ProtocolFunctionality.pid_t) List.list) : ((ProtocolFunctionality.pid_t * ProtocolFunctionality.input_t)) List.list =
                                                                                                                                                                                              (List.map (fun (pid : ProtocolFunctionality.pid_t) -> (pid , (ProtocolFunctionality.input pid xs))) pids)
    let extract_rands (rs : rands_t) (pids : (ProtocolFunctionality.pid_t) List.list) : (rand_t) List.list =
                                                                                                               (List.map (Logic.transpose (rand) rs) pids)
    let extract_traces (tr : traces_t) (pids : (ProtocolFunctionality.pid_t) List.list) : (trace_t) List.list =
                                                                                                                  (List.map (Logic.transpose (trace) tr) pids)
    let consistent_views_output (c : ProtocolFunctionality.circuit_t) (_ : ProtocolFunctionality.pinput_t) (vi : view_t) (vj : view_t) (i : ProtocolFunctionality.pid_t) (j : ProtocolFunctionality.pid_t) : Pervasive.bool =
                                                                                                                                                                                                                                (let (vi') = (from_view_t i vi) in
                                                                                                                                                                                                                                 (let (vj') = (from_view_t j vj) in
                                                                                                                                                                                                                                  (MaurerReveal.stateful_consistent_views_outputs (Aux.fst3 c) i j vi' vj')))
    let consistent_views_public_output (c : ProtocolFunctionality.circuit_t) (_ : ProtocolFunctionality.pinput_t) (vi : view_t) (vj : view_t) (i : ProtocolFunctionality.pid_t) (j : ProtocolFunctionality.pid_t) : Pervasive.bool =
                                                                                                                                                                                                                                       (let (vi') = (from_view_t i vi) in
                                                                                                                                                                                                                                        (let (vj') = (from_view_t j vj) in
                                                                                                                                                                                                                                         (let (cv) = (MaurerReveal.stateful_consistent_views_outputs (Aux.fst3 c) i j vi' vj') in
                                                                                                                                                                                                                                          (let (ci) = (MaurerProtocolFunctionality.consistent_inputs c i j (Aux.fst3 vi') (Aux.fst3 vj')) in
                                                                                                                                                                                                                                           (let (cr) = (consistent_rands' (Aux.fst3 c) (Aux.thr3 vi') (Aux.thr3 vj')) in
                                                                                                                                                                                                                                            (Pervasive.anda cv (Pervasive.anda ci cr)))))))
end
module MaurerBoolProtocolFunctionality = struct
    type circuit_t = (MaurerCircuit.circuit * (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgISet.ISet.iset))
    let rec n : Pervasive.int =
                                  (MaurerProtocolFunctionality.n)
    let rec t : Pervasive.int =
                                  (MaurerProtocolFunctionality.t)
    type pid_t = MaurerProtocolFunctionality.pid_t
    let rec pid_set : (Pervasive.int) List.list =
                                                    (MaurerProtocolFunctionality.pid_set)
    type pinput_t = MaurerProtocolFunctionality.pinput_t
    type sinput_t = MaurerProtocolFunctionality.sinput_t
    type input_t = (pinput_t * sinput_t)
    type inputs_t = ((pid_t * input_t)) List.list
    type pinputs_t = ((pid_t * pinput_t)) List.list
    type sinputs_t = ((pid_t * sinput_t)) List.list
    let input (pid : pid_t) (xs : inputs_t) : input_t =
                                                          (Logic.oget (List.assoc xs pid))
    let pinput (pid : pid_t) (xs : inputs_t) : pinput_t =
                                                            (fst (input pid xs))
    let sinput (pid : pid_t) (xs : inputs_t) : sinput_t =
                                                            (snd (input pid xs))
    let mk_inputs (xp : pinput_t) (sx : ((pid_t * sinput_t)) List.list) : ((pid_t * (pinput_t * sinput_t))) List.list =
                                                                                                                          (List.map (fun (pid : pid_t) -> (pid , (xp , (Logic.oget (List.assoc sx pid))))) (pid_set))
    let pinputs (xs : inputs_t) : ((pid_t * pinput_t)) List.list =
                                                                     (List.map (fun (pid : pid_t) -> (pid , (fst (Logic.oget (List.assoc xs pid))))) (pid_set))
    let sinputs (xs : inputs_t) : ((pid_t * sinput_t)) List.list =
                                                                     (List.map (fun (pid : pid_t) -> (pid , (snd (Logic.oget (List.assoc xs pid))))) (pid_set))
    let rec valid_circuit : (MaurerProtocolFunctionality.circuit_t -> Pervasive.bool) =
                                                                                          (MaurerProtocolFunctionality.valid_circuit)
    let rec valid_inputs : (MaurerProtocolFunctionality.circuit_t -> (MaurerProtocolFunctionality.inputs_t -> Pervasive.bool)) =
                                                                                                                                   (MaurerProtocolFunctionality.valid_inputs)
    type output_t = Pervasive.bool
    type outputs_t = ((pid_t * output_t)) List.list
    let output (pid : pid_t) (xs : outputs_t) : output_t =
                                                             (Logic.oget (List.assoc xs pid))
end
module MaurerBoolProtocol = struct
    module ProtocolFunctionality = struct
        type circuit_t = MaurerBoolProtocolFunctionality.circuit_t
        let rec n : Pervasive.int =
                                      (MaurerBoolProtocolFunctionality.n)
        let rec t : Pervasive.int =
                                      (MaurerBoolProtocolFunctionality.t)
        type pid_t = MaurerBoolProtocolFunctionality.pid_t
        let rec pid_set : (Pervasive.int) List.list =
                                                        (MaurerBoolProtocolFunctionality.pid_set)
        type pinput_t = MaurerBoolProtocolFunctionality.pinput_t
        type sinput_t = MaurerBoolProtocolFunctionality.sinput_t
        type input_t = MaurerBoolProtocolFunctionality.input_t
        type inputs_t = MaurerBoolProtocolFunctionality.inputs_t
        type pinputs_t = MaurerBoolProtocolFunctionality.pinputs_t
        type sinputs_t = MaurerBoolProtocolFunctionality.sinputs_t
        let rec input : (MaurerBoolProtocolFunctionality.pid_t -> (MaurerBoolProtocolFunctionality.inputs_t -> MaurerBoolProtocolFunctionality.input_t)) =
                                                                                                                                                             (MaurerBoolProtocolFunctionality.input)
        let rec pinput : (MaurerBoolProtocolFunctionality.pid_t -> (MaurerBoolProtocolFunctionality.inputs_t -> MaurerBoolProtocolFunctionality.pinput_t)) =
                                                                                                                                                               (MaurerBoolProtocolFunctionality.pinput)
        let rec sinput : (MaurerBoolProtocolFunctionality.pid_t -> (MaurerBoolProtocolFunctionality.inputs_t -> MaurerBoolProtocolFunctionality.sinput_t)) =
                                                                                                                                                               (MaurerBoolProtocolFunctionality.sinput)
        let rec mk_inputs : (MaurerBoolProtocolFunctionality.pinput_t -> (((MaurerBoolProtocolFunctionality.pid_t * MaurerBoolProtocolFunctionality.sinput_t)) List.list -> ((MaurerBoolProtocolFunctionality.pid_t * (MaurerBoolProtocolFunctionality.pinput_t * MaurerBoolProtocolFunctionality.sinput_t))) List.list)) =
                                                                                                                                                                                                                                                                                                                              (MaurerBoolProtocolFunctionality.mk_inputs)
        let rec pinputs : (MaurerBoolProtocolFunctionality.inputs_t -> ((MaurerBoolProtocolFunctionality.pid_t * MaurerBoolProtocolFunctionality.pinput_t)) List.list) =
                                                                                                                                                                           (MaurerBoolProtocolFunctionality.pinputs)
        let rec sinputs : (MaurerBoolProtocolFunctionality.inputs_t -> ((MaurerBoolProtocolFunctionality.pid_t * MaurerBoolProtocolFunctionality.sinput_t)) List.list) =
                                                                                                                                                                           (MaurerBoolProtocolFunctionality.sinputs)
        let rec valid_circuit : (MaurerProtocolFunctionality.circuit_t -> Pervasive.bool) =
                                                                                              (MaurerBoolProtocolFunctionality.valid_circuit)
        let rec valid_inputs : (MaurerProtocolFunctionality.circuit_t -> (MaurerProtocolFunctionality.inputs_t -> Pervasive.bool)) =
                                                                                                                                       (MaurerBoolProtocolFunctionality.valid_inputs)
        type output_t = MaurerBoolProtocolFunctionality.output_t
        type outputs_t = MaurerBoolProtocolFunctionality.outputs_t
        let rec output : (MaurerBoolProtocolFunctionality.pid_t -> (MaurerBoolProtocolFunctionality.outputs_t -> MaurerBoolProtocolFunctionality.output_t)) =
                                                                                                                                                                (MaurerBoolProtocolFunctionality.output)
    end
    type rand_t = MaurerProtocol.rand_t
    type rands_t = ((ProtocolFunctionality.pid_t * rand_t)) List.list
    let rand (pid : ProtocolFunctionality.pid_t) (rs : rands_t) : rand_t =
                                                                             (Logic.oget (List.assoc rs pid))
    let rec valid_rand : (MaurerProtocol.ProtocolFunctionality.circuit_t -> (MaurerProtocol.rand_t -> Pervasive.bool)) =
                                                                                                                           (MaurerProtocol.valid_rand)
    let valid_rands (c : ProtocolFunctionality.circuit_t) (rs : rands_t) : Pervasive.bool =
                                                                                              (Pervasive._and (Pervasive.eq (List.unzip1 rs) (ProtocolFunctionality.pid_set)) (assert false))
    type in_messages_t = MaurerProtocol.in_messages_t
    type poutput_t = MaurerProtocol.poutput_t
    type poutputs_t = ((ProtocolFunctionality.pid_t * poutput_t)) List.list
    let poutput (pid : ProtocolFunctionality.pid_t) (pouts : poutputs_t) : poutput_t =
                                                                                         (Logic.oget (List.assoc pouts pid))
    type trace_t = (poutputs_t * in_messages_t)
    type traces_t = ((ProtocolFunctionality.pid_t * trace_t)) List.list
    let trace (pid : ProtocolFunctionality.pid_t) (trs : traces_t) : trace_t =
                                                                                 (Logic.oget (List.assoc trs pid))
    type view_t = (ProtocolFunctionality.input_t * (rand_t * trace_t))
    type views_t = ((ProtocolFunctionality.pid_t * view_t)) List.list
    let view (pid : ProtocolFunctionality.pid_t) (vs : views_t) : view_t =
                                                                             (Logic.oget (List.assoc vs pid))
    let rec local_output (c : MaurerProtocol.ProtocolFunctionality.circuit_t) (i : NextMsgMaurerAPI.MaurerAPI.pid) (v : MaurerProtocol.view_t) : Pervasive.bool =
                                                                                                                                                                    (let (o) = (MaurerProtocol.local_output c i v) in
                                                                                                                                                                     (MaurerDomain.wire_to_bool o))
    let rec protocol (c : MaurerProtocol.ProtocolFunctionality.circuit_t) (rs : MaurerProtocol.rands_t) (ws : MaurerProtocol.ProtocolFunctionality.inputs_t) : (((Pervasive.int * (((Pervasive.int * Pervasive.unit)) List.list * MaurerReveal.ST.in_msgs))) List.list * ((Pervasive.int * Pervasive.bool)) List.list) =
                                                                                                                                                                                                                                                                                                                           (let (_to) = (MaurerProtocol.protocol c rs ws) in
                                                                                                                                                                                                                                                                                                                            (Aux.prod (Logic.idfun) (List.map (Aux.prod (Logic.idfun) (MaurerDomain.wire_to_bool))) _to))
    let rec consistent_views : (MaurerProtocol.ProtocolFunctionality.circuit_t -> (MaurerProtocol.view_t -> (MaurerProtocol.view_t -> (MaurerProtocol.ProtocolFunctionality.pid_t -> (MaurerProtocol.ProtocolFunctionality.pid_t -> Pervasive.bool))))) =
                                                                                                                                                                                                                                                            (MaurerProtocol.consistent_views)
    let consistent_views_public (c : ProtocolFunctionality.circuit_t) (xp : ProtocolFunctionality.pinput_t) (vi : view_t) (vj : view_t) (i : ProtocolFunctionality.pid_t) (j : ProtocolFunctionality.pid_t) : Pervasive.bool =
                                                                                                                                                                                                                                 (Pervasive._and (Pervasive.eq (fst (Aux.fst3 vi)) xp) (Pervasive._and (Pervasive.eq (fst (Aux.fst3 vj)) xp) (consistent_views c vi vj i j)))
    let consistent_trace_public (c : ProtocolFunctionality.circuit_t) (xp : ProtocolFunctionality.pinput_t) (vs : ((ProtocolFunctionality.pid_t * view_t)) List.list) : Pervasive.bool =
                                                                                                                                                                                           (assert false)
    let extract_inputs (xs : ProtocolFunctionality.inputs_t) (pids : (ProtocolFunctionality.pid_t) List.list) : ((ProtocolFunctionality.pid_t * ProtocolFunctionality.input_t)) List.list =
                                                                                                                                                                                              (List.map (fun (pid : ProtocolFunctionality.pid_t) -> (pid , (ProtocolFunctionality.input pid xs))) pids)
    let extract_rands (rs : rands_t) (pids : (ProtocolFunctionality.pid_t) List.list) : (rand_t) List.list =
                                                                                                               (List.map (Logic.transpose (rand) rs) pids)
    let extract_traces (tr : traces_t) (pids : (ProtocolFunctionality.pid_t) List.list) : (trace_t) List.list =
                                                                                                                  (List.map (Logic.transpose (trace) tr) pids)
end
