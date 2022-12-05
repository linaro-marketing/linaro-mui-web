
  import React from "react";
  import { render } from "@testing-library/react";
  import Linked from "./Linked";
  import { LinkedProps } from "./Linked.types";
  describe("Linked Test", () => {
    test("renders the Navbar component", () => {
      render(<Linked />);
    });
  });
  
  