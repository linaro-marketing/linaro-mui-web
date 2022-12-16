import React from "react";
import { render } from "@testing-library/react";
import DrawerLinks from "./DrawerLinks";
import { DrawerLinksProps } from "./DrawerLinks.types";
describe("DrawerLinks Test", () => {
  test("renders the DrawerLinks component", () => {
    render(<DrawerLinks pages={[{ title: "Baz", pathname: "/Baz" }]} />);
  });
});
