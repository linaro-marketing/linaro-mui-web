// Generated with util/create-component.js
import React from "react";
import Footer from "./Footer";
export default {
  title: "Footer",
};
const footerColumns = [
  {
    title: "Core Technologies",
    links: [
      {
        title: "Artificial Intelligence",
        pathname: "/foo",
      },
      {
        title: "Linux Kernel",
        pathname: "/bar",
      },
      {
        title: "Security",
        pathname: "/baz",
      },
      {
        title: "Testing & CI",
        pathname: "/baz",
      },
      {
        title: "Toolchain",
        pathname: "/baz",
      },
      {
        title: "Virtualization",
        pathname: "/baz",
      },
    ],
  },
  {
    links: [
      {
        title: "Projects",
        pathname: "/foo",
      },
      {
        title: "Membership",
        pathname: "/bar",
      },
      {
        title: "Services",
        pathname: "/baz",
      },
      {
        title: "Support",
        pathname: "/baz",
      },
      {
        title: "Downloads",
        pathname: "/baz",
      },
    ],
  },
  {
    links: [
      {
        title: "Blogs",
        pathname: "/foo",
      },
      {
        title: "Events",
        pathname: "/bar",
      },
      {
        title: "News",
        pathname: "/baz",
      },
      {
        title: "Careers",
        pathname: "/baz",
      },
    ],
  },
];
export const WithBar = () => <Footer columns={footerColumns} />;
export const WithBaz = () => <Footer columns={footerColumns} />;
