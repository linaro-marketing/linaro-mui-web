import React from "react";
import { render } from "@testing-library/react";
import DarkModeToggle from "./DarkModeToggle";
import { DarkModeToggleProps } from "./DarkModeToggle.types";
describe("DarkModeToggle Test", () => {
  test("renders the DarkModeToggle component", () => {
    render(
      <DarkModeToggle
        themeMode="dark"
        toggleTheme={() => {
          alert("toggleTheme");
        }}
      />
    );
  });
});
