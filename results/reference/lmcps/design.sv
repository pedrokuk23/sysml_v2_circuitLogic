module design(input clk, input apfail, input limits, input standby, input supported, output pullup, output mode, output request, output good, output autopilot, output notLimits);
  reg [1:0] apState; initial apState = 2'd0;
  wire [1:0] nextState;
  reg [1:0] senState; initial senState = 2'd0;
  wire [1:0] nextSenState;
  reg pre1_autopilot; initial pre1_autopilot = 1'b0;
  reg pre2_autopilot; initial pre2_autopilot = 1'b0;
  reg pre3_autopilot; initial pre3_autopilot = 1'b0;
  reg pre1_limits; initial pre1_limits = 1'b0;
  reg pre1_notLimits; initial pre1_notLimits = 1'b0;
  reg pre2_notLimits; initial pre2_notLimits = 1'b0;
  reg pre3_notLimits; initial pre3_notLimits = 1'b0;
  reg pre4_notLimits; initial pre4_notLimits = 1'b0;
  reg pre5_notLimits; initial pre5_notLimits = 1'b0;
  assign pullup = (2 == nextState);
  assign mode = (0 != nextState);
  assign request = ((0 == nextState) || (1 == nextState));
  assign good = (2 != senState);
  assign autopilot = ((!(standby) && supported) && !(apfail));
  assign notLimits = !(limits);
  assign nextState = (apState == 0) ? ((standby) ? 3 : ((((good && supported) && !(standby))) ? 1 : (apState))) : ((apState == 1) ? ((standby) ? 3 : (((!(good) && !(standby))) ? 2 : (apState))) : ((apState == 2) ? (((standby && good)) ? 3 : ((((supported && good) && !(standby))) ? 0 : (apState))) : ((apState == 3) ? ((apfail) ? 2 : (((!(standby) && !(apfail))) ? 0 : (apState))) : (apState))));
  assign nextSenState = (senState == 0) ? ((limits) ? 2 : (((!(request) && !(limits))) ? 1 : (senState))) : ((senState == 1) ? (((request && mode)) ? 0 : (senState)) : ((senState == 2) ? (((!(request) || !(limits))) ? 1 : (senState)) : (senState)));
  always @(posedge clk) begin
    apState <= nextState;
    senState <= nextSenState;
    pre1_autopilot <= autopilot;
    pre2_autopilot <= pre1_autopilot;
    pre3_autopilot <= pre2_autopilot;
    pre1_limits <= limits;
    pre1_notLimits <= notLimits;
    pre2_notLimits <= pre1_notLimits;
    pre3_notLimits <= pre2_notLimits;
    pre4_notLimits <= pre3_notLimits;
    pre5_notLimits <= pre4_notLimits;
  end
`ifdef P_FSM_001
  always @* assert ((!((((limits && !(standby)) && !(apfail)) && supported)) || (pullup)));
`endif
`ifdef P_FSM_001v2
  always @* assert ((!(((autopilot && pre1_autopilot) && pre1_limits)) || (pullup)));
`endif
`ifdef P_FSM_001v3
  always @* assert ((!(((((((((autopilot && pre1_autopilot) && pre2_autopilot) && pre3_autopilot) && pre2_notLimits) && pre3_notLimits) && pre4_notLimits) && pre5_notLimits) && pre1_limits)) || (pullup)));
`endif
`ifdef P_FSM_002
  always @* assert ((!(((0 == apState) && standby)) || ((3 == nextState))));
`endif
`ifdef P_FSM_003
  always @* assert ((!((((0 == apState) && good) && supported)) || ((1 == nextState))));
`endif
`ifdef P_FSM_004
  always @* assert ((!(((1 == apState) && !(good))) || ((2 == nextState))));
`endif
`ifdef P_FSM_005
  always @* assert ((!(((1 == apState) && standby)) || ((3 == nextState))));
`endif
`ifdef P_FSM_006
  always @* assert ((!((((2 == apState) && standby) && good)) || ((3 == nextState))));
`endif
`ifdef P_FSM_007
  always @* assert ((!((((2 == apState) && supported) && good)) || ((0 == nextState))));
`endif
`ifdef P_FSM_008
  always @* assert ((!(((3 == apState) && !(standby))) || ((0 == nextState))));
`endif
`ifdef P_FSM_009
  always @* assert ((!(((3 == apState) && apfail)) || ((2 == nextState))));
`endif
`ifdef P_FSM_010
  always @* assert ((!(((0 == senState) && limits)) || ((2 == nextSenState))));
`endif
`ifdef P_FSM_011
  always @* assert ((!(((0 == senState) && !(request))) || ((1 == nextSenState))));
`endif
`ifdef P_FSM_012
  always @* assert ((!((((2 == senState) && !(request)) && !(limits))) || ((1 == nextSenState))));
`endif
`ifdef P_FSM_013
  always @* assert ((!((((1 == senState) && request) && mode)) || ((0 == nextSenState))));
`endif
endmodule
