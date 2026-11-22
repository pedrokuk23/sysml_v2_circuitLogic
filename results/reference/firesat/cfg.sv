module cfg(input payload_b0, input orbit_b0, input bus_b0, input ground_b0, input comm_b0, input onboard_detect, input onboard_geolocate, output r_MR_RES, output r_MR_TL, output r_MR_MASS, output r_CAP, output legal, output valid);
  assign r_MR_RES = !orbit_b0;
  assign r_MR_TL = comm_b0 || orbit_b0 || (ground_b0 && onboard_detect);
  assign r_MR_MASS = bus_b0 || !payload_b0;
  assign r_CAP = bus_b0 || !onboard_detect || !onboard_geolocate;
  assign legal = 1'b1;
  assign valid = legal && r_MR_RES && r_MR_TL && r_MR_MASS && r_CAP;
`ifdef DEAD_payload_smallIR
  always @* assert (!(valid && payload_b0 == 1'b0));
`endif
`ifdef CORE_payload_smallIR
  always @* assert (!valid || (payload_b0 == 1'b0));
`endif
`ifdef DEAD_payload_largeIR
  always @* assert (!(valid && payload_b0 == 1'b1));
`endif
`ifdef CORE_payload_largeIR
  always @* assert (!valid || (payload_b0 == 1'b1));
`endif
`ifdef DEAD_orbit_leo2
  always @* assert (!(valid && orbit_b0 == 1'b0));
`endif
`ifdef CORE_orbit_leo2
  always @* assert (!valid || (orbit_b0 == 1'b0));
`endif
`ifdef DEAD_orbit_geo1
  always @* assert (!(valid && orbit_b0 == 1'b1));
`endif
`ifdef CORE_orbit_geo1
  always @* assert (!valid || (orbit_b0 == 1'b1));
`endif
`ifdef DEAD_bus_smallBus
  always @* assert (!(valid && bus_b0 == 1'b0));
`endif
`ifdef CORE_bus_smallBus
  always @* assert (!valid || (bus_b0 == 1'b0));
`endif
`ifdef DEAD_bus_midBus
  always @* assert (!(valid && bus_b0 == 1'b1));
`endif
`ifdef CORE_bus_midBus
  always @* assert (!valid || (bus_b0 == 1'b1));
`endif
`ifdef DEAD_ground_gs4
  always @* assert (!(valid && ground_b0 == 1'b0));
`endif
`ifdef CORE_ground_gs4
  always @* assert (!valid || (ground_b0 == 1'b0));
`endif
`ifdef DEAD_ground_gs12
  always @* assert (!(valid && ground_b0 == 1'b1));
`endif
`ifdef CORE_ground_gs12
  always @* assert (!valid || (ground_b0 == 1'b1));
`endif
`ifdef DEAD_comm_direct
  always @* assert (!(valid && comm_b0 == 1'b0));
`endif
`ifdef CORE_comm_direct
  always @* assert (!valid || (comm_b0 == 1'b0));
`endif
`ifdef DEAD_comm_relayLink
  always @* assert (!(valid && comm_b0 == 1'b1));
`endif
`ifdef CORE_comm_relayLink
  always @* assert (!valid || (comm_b0 == 1'b1));
`endif
endmodule
