import React from "react";
import { render } from "@testing-library/react";
import DrawerLinks from "./DrawerLinks";
import { DrawerLinksProps } from "./DrawerLinks.types";
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
    subMenus: [
      {
        title: "Membership Overview",
        pathname: "/membership/",
      },
      {
        title: "Group Membership",
        pathname: "/membership/groups/",
      },
      {
        title: "Projects",
        pathname: "/projects/",
      },
      {
        title: "Windows on Arm Group",
        pathname: "/windows-on-arm/",
      },
      {
        title: "Community Projects",
        pathname: "/community-projects/",
      },
    ],
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
describe("DrawerLinks Test", () => {
  test("renders the DrawerLinks component", () => {
    render(<DrawerLinks pages={examplePages} />);
  });
});
