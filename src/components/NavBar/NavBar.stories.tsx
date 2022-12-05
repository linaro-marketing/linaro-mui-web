// Generated with util/create-component.js
import React from "react";
import NavBar from "./NavBar";
export default {
  title: "NavBar",
};
export const WithBar = () => (
  <NavBar
    logo="https://www.linaro.org/assets/images/Linaro-Logo.svg"
    pages={[{ name: "Bar", link: "/bar" }]}
  />
);
export const WithBaz = () => (
  <NavBar
    logo="https://www.linaro.org/assets/images/Linaro-Logo.svg"
    pages={[{ name: "Baz", link: "/Baz" }]}
  />
);
