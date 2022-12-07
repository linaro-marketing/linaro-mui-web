// Generated with util/create-component.js
import React from "react";
import Linked from "./Linked";
export default {
  title: "Core/Linked",
  component: Linked,
  argTypes: {
    to: {
      options: ["https://google.com", "https://www.google.com"],
      control: { type: "radio" },
    },
  },
};
/**
 * Test
 * @returns
 */
export const WithGoogle = () => (
  <Linked to="https://google.com" textLink>
    {"To Google"}
  </Linked>
);
export const WithBing = () => (
  <Linked to="https://bing.com">{"To Bing"}</Linked>
);
