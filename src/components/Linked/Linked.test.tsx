import React from "react";
import { render } from "@testing-library/react";
import Linked from "./Linked";
describe("Linked Test", () => {
  test("renders the Linked component", () => {
    render(<Linked to={"/"}>Test</Linked>);
  });
});
