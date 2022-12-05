import React from "react";
import { render } from "@testing-library/react";
import NavBar from "./NavBar";
import { NavBarProps } from "./NavBar.types";
describe("NavBar Test", () => {
  test("renders the Navbar component", () => {
    render(
      <NavBar
        settings={[{ name: "Baz", link: "/Baz" }]}
        pages={[{ name: "Baz", link: "/Baz" }]}
      />
    );
  });
});
