module arbiter(
  input logic clk,
  input logic rst,
  input logic req0,
  input logic req1,
  output logic grant0,
  output logic grant1
);
  logic past_valid = 1'b0;

  always_ff @(posedge clk) begin
    past_valid <= 1'b1;

    // The environment supplies exactly one reset cycle. Requests remain free.
    if ($initstate)
      assume(rst);
    else
      assume(!rst);

    if (rst) begin
      grant0 <= 1'b0;
      grant1 <= 1'b0;
    end else begin
      // req0 has deterministic priority when both requests are high.
      grant0 <= req0;
      grant1 <= !req0 && req1;
    end

    if (past_valid && !$past(rst)) begin
      assert(!(grant0 && grant1));
      // Confirm that simultaneous requests are not excluded by assumptions.
      cover($past(req0) && $past(req1) && grant0 && !grant1);
    end
  end
endmodule
