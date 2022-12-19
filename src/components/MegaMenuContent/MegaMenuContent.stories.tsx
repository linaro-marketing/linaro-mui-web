// Generated with util/create-component.js
import React from "react";
import MegaMenuContent from "./MegaMenuContent";
export default {
  title: "MegaMenuContent",
};
export const WithBar = () => (
  <MegaMenuContent
    content={{
      sections: [
        {
          title: "Automotive, IoT & Edge Devices",
          options: [
            {
              title: "Client Devices",
              pathname: "/client-devices/",
            },
            {
              title: "Cloud Computing & Servers",
              pathname: "/cloud-computing-and-servers/",
            },
          ],
        },
        {
          title: "Automotive, IoT & Edge Devices",
          options: [
            {
              title: "Client Devices",
              pathname: "/client-devices/",
            },
            {
              title: "Cloud Computing & Servers",
              pathname: "/cloud-computing-and-servers/",
            },
          ],
        },
      ],
    }}
  />
);
export const WithBaz = () => <MegaMenuContent foo="baz" />;
