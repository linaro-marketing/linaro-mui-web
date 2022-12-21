
  import React from "react";
  import { render } from "@testing-library/react";
  import Footer from "./Footer";
  import { FooterProps } from "./Footer.types";
  describe("Footer Test", () => {
    test("renders the Footer component", () => {
      render(<Footer />);
    });
  });
  
  