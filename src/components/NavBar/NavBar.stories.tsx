// Generated with util/create-component.js
import React from "react";
import NavBar from "./NavBar";
export default {
  title: "Core/Navigation/NavBar",
  component: NavBar,
};

const examplePages = [
  {
    title: "Solutions",
    subMenus: [
      {
        title: "Automotive, IoT & Edge Devices",
        pathname: "/automotive-iot-and-edge-devices/",
      },
      {
        title: "Client Devices",
        pathname: "/client-devices/",
      },
      {
        title: "Cloud Computing & Servers",
        pathname: "/cloud-computing-and-servers/",
      },

      {
        title: "Overview",
        pathname: "/core-technologies/",
      },
      {
        title: "Artificial Intelligence",
        pathname: "/core-technologies/artificial-intelligence/",
      },
      {
        title: "Linux Kernel",
        pathname: "/core-technologies/linux-kernel/",
      },
      {
        title: "Security",
        pathname: "/core-technologies/security/",
      },
      {
        title: "Testing & CI",
        pathname: "/core-technologies/testing-and-ci/",
      },
      {
        title: "Toolchain",
        pathname: "/core-technologies/toolchain/",
      },
      {
        title: "Virtualization",
        pathname: "/core-technologies/virtualization/",
      },
    ],
  },
  {
    title: "Membership",
    type: "megamenu",
    megaMenuContent: {
      sections: [
        {
          title: "Core Technologies",
          options: [
            {
              title: "Client Devices",
              description:
                "Client devices are the most common type of device in the world.",
              pathname: "/client-devices/",
            },
            {
              title: "Cloud Computing & Servers",
              description:
                "Cloud computing is the on-demand delivery of IT resources.",
              pathname: "/cloud-computing-and-servers/",
            },
            {
              title: "Servers",
              description:
                "Servers are the backbone of the cloud computing infrastructure.",
              pathname: "/client-devices/",
            },
            {
              title: "Client Devices",
              description:
                "Client devices are the most common type of device in the world.",
              pathname: "/client-devices/",
            },
            {
              title: "Cloud Computing & Servers",
              description:
                "Cloud computing is the on-demand delivery of IT resources.",
              pathname: "/cloud-computing-and-servers/",
            },
            {
              title: "Servers",
              description:
                "Servers are the backbone of the cloud computing infrastructure.",
              pathname: "/client-devices/",
            },
          ],
        },
      ],
    },
  },
  {
    title: "Services",
    subMenus: [
      {
        title: "Overview",
        pathname: "/services/",
      },
      {
        title: "Hands on training",
        pathname: "/services/hands-on-training/",
      },
      {
        title: "Security",
        pathname: "/services/security/",
      },
      {
        title: "Testing & Long term support",
        pathname: "/services/testing-and-long-term-support/",
      },
      {
        title: "Board Support Packages",
        pathname: "/services/board-support-packages/",
      },
      {
        title: "System Performance & Optimization",
        pathname: "/services/system-performance-and-optimization/",
      },
      {
        title: "Qualcomm Platform Services",
        pathname: "/services/qualcomm-platforms-services/",
      },
    ],
  },
  {
    title: "Resources",
    subMenus: [
      {
        title: "Downloads",
        pathname: "/downloads/",
      },
      {
        title: "Whitepapers",
        pathname: "/whitepapers/",
      },
      {
        title: "Learning Hub",
        pathname: "/learning-hub/",
      },
      {
        title: "Linaro Resources Hub",
        pathname: "https://resources.linaro.org",
      },
    ],
  },
  {
    title: "Support",
    pathname: "/support/",
  },
  {
    title: "About",
    subMenus: [
      {
        title: "About Linaro",
        pathname: "/about/",
      },
      {
        title: "Team",
        pathname: "/about/team/",
      },
      {
        title: "Technical Steering Committee",
        pathname: "/tsc/",
      },
      {
        title: "Contact us",
        pathname: "/contact/",
      },
      {
        title: "Linaro Connect",
        pathname: "/connect/",
      },
      {
        title: "Careers",
        pathname: "/careers/",
      },
      {
        title: "Blogs",
        pathname: "/blog/",
      },
      {
        title: "News",
        pathname: "/news/",
      },
      {
        title: "Events",
        pathname: "/events/",
      },
    ],
  },
];
export const Primary = () => (
  <NavBar
    logo="https://www.linaro.org/assets/images/Linaro-Logo.svg"
    logoLink="/"
    color="primary"
    pages={examplePages}
    darkModeToggle
    toggleTheme={() => {}}
    themeMode="dark"
  />
);
Primary.parameters = {
  layout: "fullscreen",
};

export const Secondary = () => (
  <NavBar
    logoLink="/"
    logo="https://www.linaro.org/assets/images/Linaro-Logo.svg"
    pages={examplePages}
    darkModeToggle
    toggleTheme={() => {}}
    themeMode="dark"
  />
);
Secondary.parameters = {
  layout: "fullscreen",
};
