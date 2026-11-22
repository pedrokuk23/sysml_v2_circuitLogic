module miter(input [1:0] apState, input apfail, input good, input limits, input [1:0] nextSenState, input [1:0] nextState, input request, input [1:0] senState, input standby, input supported, output old_FSM_003, output new_FSM_003, output old_FSM_004, output new_FSM_004, output old_FSM_007, output new_FSM_007, output old_FSM_008, output new_FSM_008, output old_FSM_011, output new_FSM_011, output old_FSM_012, output new_FSM_012);
  assign old_FSM_003 = (!((((0 == apState) && good) && supported)) || ((1 == nextState)));
  assign new_FSM_003 = (!(((((0 == apState) && good) && supported) && !(standby))) || ((1 == nextState)));
`ifdef M_FSM_003
  always @* assert (old_FSM_003 == new_FSM_003);
`endif
  assign old_FSM_004 = (!(((1 == apState) && !(good))) || ((2 == nextState)));
  assign new_FSM_004 = (!((((1 == apState) && !(good)) && !(standby))) || ((2 == nextState)));
`ifdef M_FSM_004
  always @* assert (old_FSM_004 == new_FSM_004);
`endif
  assign old_FSM_007 = (!((((2 == apState) && supported) && good)) || ((0 == nextState)));
  assign new_FSM_007 = (!(((((2 == apState) && supported) && good) && !(standby))) || ((0 == nextState)));
`ifdef M_FSM_007
  always @* assert (old_FSM_007 == new_FSM_007);
`endif
  assign old_FSM_008 = (!(((3 == apState) && !(standby))) || ((0 == nextState)));
  assign new_FSM_008 = (!((((3 == apState) && !(standby)) && !(apfail))) || ((0 == nextState)));
`ifdef M_FSM_008
  always @* assert (old_FSM_008 == new_FSM_008);
`endif
  assign old_FSM_011 = (!(((0 == senState) && !(request))) || ((1 == nextSenState)));
  assign new_FSM_011 = (!((((0 == senState) && !(request)) && !(limits))) || ((1 == nextSenState)));
`ifdef M_FSM_011
  always @* assert (old_FSM_011 == new_FSM_011);
`endif
  assign old_FSM_012 = (!((((2 == senState) && !(request)) && !(limits))) || ((1 == nextSenState)));
  assign new_FSM_012 = (!(((2 == senState) && (!(request) || !(limits)))) || ((1 == nextSenState)));
`ifdef M_FSM_012
  always @* assert (old_FSM_012 == new_FSM_012);
`endif
endmodule
