// ============================================================
// weighted_round_robin_sva.sv
// SVA checker for weighted_round_robin
//  - Environment assumptions to bound state space
//  - Basic interface sanity assertions
//  - Functional assertions vs reference model
//  - Fairness + cover properties
//  - Reference model for functional checking
// ============================================================
`default_nettype none

module weighted_round_robin_sva #(
  parameter int N = 8,
  parameter int W = 3
)(
  input  logic                 i_clk,
  input  logic                 i_rstn,       // active-LOW reset
  input  logic                 i_en,
  input  logic [N-1:0]         i_req,
  input  logic                 i_load,
  input  logic [N-1:0][W-1:0]  i_weights,
  input  logic [N-1:0]         o_gnt
);

  // ------------------------------------------------------------
  // Local params
  // ------------------------------------------------------------
  localparam int M          = $clog2(N);
  localparam int MAX_WEIGHT = (1 << W) - 1;
  localparam int FAIR_BOUND = ((MAX_WEIGHT - 1) * (N - 1)); // optional bound
  localparam int MAX_LAT    = N * (1 << W);

  default clocking cb @(posedge i_clk); endclocking

  // ------------------------------------------------------------
  // Reference model state (mirrors TB behavior)
  // ------------------------------------------------------------
  logic [N-1:0][W-1:0] ref_weight;
  logic [M-1:0]        ref_ptr;
  logic [N-1:0]        ref_gnt;
  logic [M-1:0]        ref_winner_idx;

  logic [N-1:0][W-1:0] masked_ref;
  logic [W-1:0]        max_ref;
  logic [N-1:0]        req_w_ref;
  logic [N-1:0]        next_gnt_ref;
  logic [M-1:0]        next_winner_ref;
  logic                found_ref;
  int                  current_idx_ref;

  function automatic bit ref_all_zero;
    bit allz = 1'b1;
    for (int i = 0; i < N; i++) begin
      if (ref_weight[i] != '0) allz = 1'b0;
    end
    return allz;
  endfunction

  // ============================================================
  // 1. ENVIRONMENT ASSUMPTIONS
  // ============================================================

  // A_env1: Inputs are 2-state (no X/Z).
  property a_no_unknown_inputs;
    @(posedge i_clk) disable iff (!i_rstn)
      !$isunknown({i_en, i_load, i_req, i_weights});
  endproperty
  assume property (a_no_unknown_inputs);


    //A_env2: Weights loaded are within the legal range [0 .. MAX_WEIGHT]., TOOL INHERENTLY DOES IT, no need for this
//  genvar wa;
//  generate
 //   for (wa = 0; wa < N; wa++) begin : gen_a_weight_in_range
   //   property a_weight_in_range;
   //     @(posedge i_clk) disable iff (!i_rstn)
    //      i_load |-> (i_weights[wa] <= MAX_WEIGHT[W-1:0]);
    //  endproperty
   //   assume property (a_weight_in_range);
  //  end
 // endgenerate

  // A_env3: Load is a reasonable pulse not held high forever,         LOAD CAN STAY HIGH, THIS IS VALID BEHAVIOUR BEING CONSTRAINED
 // property a_load_not_stuck_high;
   // @(posedge i_clk) disable iff (!i_rstn)
     // i_load |-> ##[1:$] !i_load;
  //endproperty
  //assume property (a_load_not_stuck_high);



  // ============================================================
  // 2. REFERENCE MODEL
  // ============================================================

  // Combinational: masking, max, weighted request, RR selection
  always_comb begin
    // mask by req
    for (int i = 0; i < N; i++) begin
      masked_ref[i] = (i_req[i]) ? ref_weight[i] : '0;
    end

    // max over masked_ref
    max_ref = '0;
    for (int i = 0; i < N; i++) begin
      if (masked_ref[i] > max_ref)
        max_ref = masked_ref[i];
    end

    // req_w_ref: only max-weight active requesters
    req_w_ref = '0;
    for (int i = 0; i < N; i++) begin
      if ((masked_ref[i] == max_ref) && i_req[i])
        req_w_ref[i] = 1'b1;
    end

    // RR selection from ref_ptr
    next_gnt_ref    = '0;
    next_winner_ref = ref_ptr;
    found_ref       = 1'b0;

    if (|req_w_ref) begin
      for (int i = 0; i < N; i++) begin
        current_idx_ref = (ref_ptr + i) % N;
        if (req_w_ref[current_idx_ref] && !found_ref) begin
          next_gnt_ref[current_idx_ref] = 1'b1;
          next_winner_ref               = current_idx_ref[M-1:0];
          found_ref                     = 1'b1;
        end
      end
    end
  end

  // Sequential: weights, pointer, registered grant
  always_ff @(posedge i_clk or negedge i_rstn) begin
    if (!i_rstn) begin
      ref_weight     <= '0;
      ref_ptr        <= '0;
      ref_gnt        <= '0;
      ref_winner_idx <= '0;
    end
    else begin
      // load weights
      if (i_load) begin
        ref_weight <= i_weights;
      end
      // decrement winner when arbitration happens
      else if (i_en && (|next_gnt_ref) && (ref_weight[next_winner_ref] > 0)) begin
        ref_weight[next_winner_ref] <= ref_weight[next_winner_ref] - 1'b1;
      end

      // pointer + grant update only when enabled
      if (i_en) begin
        ref_gnt        <= next_gnt_ref;
        ref_winner_idx <= next_winner_ref;

        if (next_winner_ref == N-1)
          ref_ptr <= '0;
        else
          ref_ptr <= next_winner_ref + 1'b1;
      end
    end
  end

  // ============================================================
  // 3. BASIC INTERFACE ASSERTIONS (sanity checks)
  // ============================================================

  // Sticky "has requested sometime" latch 
  logic [N-1:0] sticky_req;

  always_ff @(posedge i_clk or negedge i_rstn) begin
    if (!i_rstn)
      sticky_req <= '0;
    else
      sticky_req <= sticky_req | i_req;   // once 1, stays 1
  end

  // A1: Grant is one-hot or zero.
  property p_grant_onehot0;
    @(posedge i_clk) disable iff (!i_rstn)
      $onehot0(o_gnt);
  endproperty
  assert property (p_grant_onehot0);


  // A2: No grant when no requests and arbiter enabled.
  property p_no_grant_without_req;
    @(posedge i_clk) disable iff (!i_rstn)
      i_en && !i_load && (i_req == '0) |=> (o_gnt == '0);
  endproperty
  assert property (p_no_grant_without_req);

  // A3: When a grant bit rises, that master must have requested sometime since reset.
  genvar gi;
  generate
    for (gi = 0; gi < N; gi++) begin : gnt_has_past_req_ben
      property p_gnt_has_past_req;
        @(posedge i_clk) disable iff (!i_rstn)
          $rose(o_gnt[gi]) |-> sticky_req[gi];
      endproperty
      ap_gnt_has_past_req: assert property (p_gnt_has_past_req);

      // cover: this grant bit ever rises
      property c_grant_bit_reached;
        @(posedge i_clk) disable iff (!i_rstn)
          $rose(o_gnt[gi]);
      endproperty
      cover property (c_grant_bit_reached);
    end
  endgenerate

  // A4: If exactly one requester is active and we arbitrate,
  //     that requester is granted next cycle.
  property p_single_request_served;
    @(posedge i_clk) disable iff (!i_rstn)
      i_en && !i_load && $onehot(i_req) |=> (o_gnt == $past(i_req));
  endproperty
  assert property (p_single_request_served);

  // A5: When disabled and not loading, grant holds its previous value.
  property p_grant_stable_when_disabled;
    @(posedge i_clk) disable iff (!i_rstn)
      !i_en && !i_load |=> (o_gnt == $past(o_gnt));
  endproperty
  assert property (p_grant_stable_when_disabled);

  // A6: Grant never goes X/Z.
  property p_gnt_no_unknown;
    @(posedge i_clk) disable iff (!i_rstn)
      !$isunknown(o_gnt);
  endproperty
  assert property (p_gnt_no_unknown);

  // ============================================================
  // 4. ASSERTIONS RTL vs REFERENCE MODEL
  // ============================================================

  // F1: After load, ref_weight becomes the previous cycle's i_weights.  WRITE THIS TO CHECK THE dut.weight_counters
//  property p_ref_weights_follow_load;
  //  @(posedge i_clk) disable iff (!i_rstn)
    //  i_load |=> (ref_weight == $past(i_weights));
 // endproperty
  //assert property (p_ref_weights_follow_load);

  // F2: DUT grant matches reference grant (both 1-cycle registered).
  property p_dut_grant_matches_ref;
    @(posedge i_clk) disable iff (!i_rstn)
      i_en && !i_load |=> (o_gnt == ref_gnt);
  endproperty
  assert property (p_dut_grant_matches_ref);

  // F3: If ref sees no winner, DUT must not assert grant. REDUNDANT, F2 CHECKS THIS
 // property p_no_grant_when_no_ref_winner;
   // @(posedge i_clk) disable iff (!i_rstn)
     // i_en && !i_load && (ref_gnt == '0) |-> (o_gnt == '0);
  //endproperty
  //assert property (p_no_grant_when_no_ref_winner);


  // F4: When a grant bit rises, the winner's weight at arbitration time
  //     is at least the maximum weight among active requesters.
  genvar gw2;
  generate
    for (gw2 = 0; gw2 < N; gw2++) begin : gen_p_grant_to_max_weight
      property p_grant_to_max_weight;
        @(posedge i_clk) disable iff (!i_rstn)
          $rose(o_gnt[gw2])
            |-> ($past(ref_weight[gw2]) >= $past(max_ref));
      endproperty
      assert property (p_grant_to_max_weight);

      property c_grant_bit_max_check;
        @(posedge i_clk) disable iff (!i_rstn)
          $rose(o_gnt[gw2]);
      endproperty
      cover property (c_grant_bit_max_check);
    end
  endgenerate

  // ============================================================
  // 5. EVENTUAL GRANT
  // ============================================================
  genvar fi;
  generate
    for (fi = 0; fi < N; fi++) begin : gen_p_fairness
      // If this requester keeps asking with non-zero tokens while enabled,
      // it must eventually be granted.
    property p_bounded_fairness_i;
            @(posedge i_clk) disable iff (!i_rstn)
              (i_en && !i_load && i_req[fi] && (ref_weight[fi] != '0)) [*1:MAX_LAT] |-> ##[1:MAX_LAT] o_gnt[fi];
    endproperty
   assert property (p_bounded_fairness_i);

      property c_fairness_antecedent_seen;
        @(posedge i_clk) disable iff (!i_rstn)
          i_en && !i_load && i_req[fi] && (ref_weight[fi] != '0);
      endproperty
      cover property (c_fairness_antecedent_seen);
    end
  endgenerate

  // ============================================================
  // 6. Cover properties
  // ============================================================

  // C1: Active grant event when there are requests.
  property c_any_active_grant;
    @(posedge i_clk) disable iff (!i_rstn)
      i_en && !i_load && (i_req != '0) && (o_gnt != '0);
  endproperty
  cover property (c_any_active_grant);

  // C2: Each requester eventually gets a grant at least once.
  genvar cv;
  generate
    for (cv = 0; cv < N; cv++) begin : gen_c_each_gets_grant
      property c_req_cv_gets_grant;
        @(posedge i_clk) disable iff (!i_rstn)
          ##[1:$] o_gnt[cv];
      endproperty
      cover property (c_req_cv_gets_grant);
    end
  endgenerate

endmodule


