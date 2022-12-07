// Generated with util/create-component.js
import React from "react";
import IconButton from "@mui/material/IconButton";
import { dashboardLinksIconMapper } from "lib/icons";
import { DarkModeToggleProps } from "./DarkModeToggle.types";
const DarkModeToggle: React.FC<DarkModeToggleProps> = ({
  variant,
  themeMode,
  toggleTheme,
}) => {
  const Brightness4Icon = dashboardLinksIconMapper["brightness4"];
  const Brightness7Icon = dashboardLinksIconMapper["brightness7"];
  const TextVariant = () => {
    return (
      <>
        {"common.youAreIn"}{" "}
        {themeMode == "dark" ? "common.darkMode" : "common.lightMode"}{" "}
        <IconButton
          aria-label={"common.toggle"}
          onClick={toggleTheme}
          size="large"
        >
          {themeMode === "light" ? <Brightness7Icon /> : <Brightness4Icon />}
        </IconButton>
      </>
    );
  };
  const IconVariant = () => {
    return (
      <>
        <IconButton
          aria-label={"common.toggle"}
          onClick={toggleTheme}
          size="large"
        >
          {themeMode === "light" ? <Brightness7Icon /> : <Brightness4Icon />}
        </IconButton>
      </>
    );
  };
  return <span>{variant === "text" ? <TextVariant /> : <IconVariant />}</span>;
};
export default DarkModeToggle;
