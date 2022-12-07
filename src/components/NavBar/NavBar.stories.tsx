// Generated with util/create-component.js
import React from "react";
import NavBar from "./NavBar";
export default {
  title: "Core/NavBar",
  component: NavBar,
};
export const Primary = () => (
  <NavBar
    logo="https://www.linaro.org/assets/images/Linaro-Logo.svg"
    logoLink="/"
    color="primary"
    pages={[
      { title: "About", link: "/about" },
      { title: "Projects", link: "/projects" },
      { title: "Solutions", link: "/solutions" },
      { title: "Services", link: "/services" },
      { title: "Resources", link: "/resources" },
    ]}
  />
);
export const Secondary = () => (
  <NavBar
    logoLink="/"
    logo="https://www.linaro.org/assets/images/Linaro-Logo.svg"
    pages={[
      { title: "About", link: "/about" },
      { title: "Projects", link: "/projects" },
      { title: "Solutions", link: "/solutions" },
      { title: "Services", link: "/services" },
      { title: "Resources", link: "/resources" },
    ]}
  />
);
