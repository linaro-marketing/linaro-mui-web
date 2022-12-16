// Generated with util/create-component.js
import React, { useState } from "react";
import DropdownMenuItem from "./DropdownMenuItem";
export default {
  title: "Core/Navigation/DropdownMenuItem",
};
export const WithSolutions = () => {
  const [menuShowingDropdown, setMenuShowingDropdown] = useState("");
  return (
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
      menuShowingDropdown={menuShowingDropdown}
      setMenuShowingDropdown={setMenuShowingDropdown}
    />
  );
};
