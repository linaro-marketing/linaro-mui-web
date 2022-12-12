import React from "react";
import { render } from "@testing-library/react";
import DropdownMenuItem from "./DropdownMenuItem";
import { DropdownMenuItemProps } from "./DropdownMenuItem.types";
describe("DropdownMenuItem Test", () => {
  test("renders the DropdownMenuItem component", () => {
    render(
      <DropdownMenuItem
        menuItem={{
          title: "Solutions",
          subMenus: [
            {
              title: "Linaro Connect",
              pathname: "/products/linaro-connect",
            },
            {
              title: "Linaro Engineering",
              pathname: "/products/linaro-engineering",
            },
          ],
        }}
        menuShowingDropdown={""}
        setMenuShowingDropdown={() => {}}
      />
    );
  });
});
