// Generated with util/create-component.js
import React from "react";
import DarkModeToggle from "./DarkModeToggle";
export default {
  title: "Core/DarkModeToggle",
};
export const WithBar = () => (
  <DarkModeToggle
    themeMode="dark"
    toggleTheme={() => {
      alert("toggleTheme");
    }}
  />
);
export const WithBaz = () => (
  <DarkModeToggle
    themeMode="dark"
    toggleTheme={() => {
      alert("toggleTheme");
    }}
  />
);
