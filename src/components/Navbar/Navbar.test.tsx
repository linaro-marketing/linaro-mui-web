import React from "react";
import { render } from "@testing-library/react";

import Navbar from "./Navbar";

describe("Button", () => {
  test("renders the Navbar component", () => {
    render(<Navbar />);
  });
});
